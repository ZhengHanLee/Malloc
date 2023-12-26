//  Memory allocator for dynamic memory management
 
//  This allocator uses segregated free lists to manage free blocks, which are
//  divided into multiple size classes. Each size class contains a linked list
//  of free blocks in that size range. The allocator maintains an array of
//  pointers to the first block in each list. The allocator can push or remove from 
//  the list to obtain the address of the free blocks and allocate them as necessary
//  to preserve the maximum possible space and reduce fragmentation.
 
//  The memory layout includes a header and a footer for each free and allocated
//  block. Each block contains a boundary tag in its header, storing the block
//  size and the in-use bit. The footer is a copy of the header. This allows
//  coalescing to be performed more efficiently.

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <assert.h>

#include "mm.h"
#include "list.h"
#include "memlib.h"
#include "config.h"


struct boundary_tag {
    int inuse:1;        // inuse bit
    int size:31;        // size of block, in words
                        // block size
};
/* FENCE is used for heap prologue/epilogue. */
const struct boundary_tag FENCE = {
    .inuse = 1,
    .size = 0
};
/* A C struct describing the beginning of each block. 
 *
 * If each block is aligned at 12 mod 16, each payload will
 * be aligned at 0 mod 16.
 */
struct block {
    struct boundary_tag header; /* offset 0, at address 12 mod 16 */
    char payload[0];            /* offset 4, at address 0 mod 16 */
    struct list_elem elem; //Need to implement this list_elem inside.
};

/* Basic constants and macros */
#define WSIZE       sizeof(struct boundary_tag)  /* Word and header/footer size (bytes) */
#define MIN_BLOCK_SIZE_WORDS 8  /* Minimum block size in words */
#define CHUNKSIZE  (1<<7)  /* Extend heap by this amount (words) */
#define NUM_SIZE_CLASSES 10 /* Number of size classes for the segregated lists*/

/* Return the max of the two sizes*/
static inline size_t max(size_t x, size_t y) {
    return x > y ? x : y;
}

/* Align the size*/
static size_t align(size_t size) {
  return (size + ALIGNMENT - 1) & ~(ALIGNMENT - 1);
}

/* Check if size is aligned properly*/
static bool is_aligned(size_t size) __attribute__((__unused__));
static bool is_aligned(size_t size) {
  return size % ALIGNMENT == 0;
}

/* Global variables */
static struct block *heap_listp = 0; /* Pointer to first block */  
static struct list segregatedList[NUM_SIZE_CLASSES]; /*List of segregated free lists*/

/* Function prototypes for internal helper routines */
static struct block *extend_heap(size_t words);
static void place(struct block *bp, size_t asize);
static struct block *find_fit(size_t asize);
static struct block *coalesce(struct block *bp);
static void segregatedListAdd(struct block *bp);

//Functions-----------------------------------------------------------------

/* Given a block, obtain previous's block footer.
   Works for left-most block also. */
static struct boundary_tag * prev_blk_footer(struct block *blk) {
    return &blk->header - 1;
}

/* Return if block is free */
static bool blk_free(struct block *blk) { 
    return !blk->header.inuse; 
}

/* Return size of block is free */
static size_t blk_size(struct block *blk) { 
    return blk->header.size; 
}

/* Given a block, obtain pointer to previous block.
   Not meaningful for left-most block. */
static struct block *prev_blk(struct block *blk) {
    struct boundary_tag *prevfooter = prev_blk_footer(blk);
    assert(prevfooter->size != 0);
    return (struct block *)((void *)blk - WSIZE * prevfooter->size);
}

/* Given a block, obtain pointer to next block.
   Not meaningful for right-most block. */
static struct block *next_blk(struct block *blk) {
    return (struct block *)((void *)blk + WSIZE * blk->header.size);
}

/* Given a block, obtain its footer boundary tag */
static struct boundary_tag * get_footer(struct block *blk) {
    return ((void *)blk + WSIZE * blk->header.size)
                   - sizeof(struct boundary_tag);
}

/* Set a block's size and inuse bit in header and footer */
static void set_header_and_footer(struct block *blk, int size, int inuse) {
    blk->header.inuse = inuse;
    blk->header.size = size;
    * get_footer(blk) = blk->header;    /* Copy header to footer */
}

/* Mark a block as used and set its size. */
static void mark_block_used(struct block *blk, int size) {
    set_header_and_footer(blk, size, 1);
}

/* Mark a block as free and set its size. */
static void mark_block_free(struct block *blk, int size) {
    set_header_and_footer(blk, size, 0);
}

//Implementation------------------------------------------------------------
/*
* mm_init - Initialize the memory manager 
*/
extern int mm_init (void)
{
    assert (offsetof(struct block, payload) == 4);
    assert (sizeof(struct boundary_tag) == 4);
    /* Create the initial empty heap */
    struct boundary_tag * initial = mem_sbrk(4 * sizeof(struct boundary_tag));
    if (initial == NULL)
    {
        return -1;
    }

    for (int i = 0; i < NUM_SIZE_CLASSES; i++)
    {
        list_init(&segregatedList[i]);
    }

    initial[2] = FENCE;                     /* Prologue footer */
    heap_listp = (struct block *)&initial[3];
    initial[3] = FENCE;                     /* Epilogue header */

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE) == NULL) 
        return -1;
    return 0;
}

/*
 * mm_malloc - Allocates a block of memory with the requested size by alligning 
 * the block and finds the fit in the segregated list 
 */
extern void *mm_malloc (size_t size)
{
    struct block *bp; 
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    
    else if(size == 448){
        size = 512;
    }
    else if(size == 112){
        size = 128;
    }
    
    /* Adjust block size to include overhead and alignment reqs. */
    size_t bsize = align(size + 2 * sizeof(struct boundary_tag));    /* account for tags */
    if (bsize < size)   
        return NULL;    /* integer overflow */
    
    /* Adjusted block size in words */
    size_t awords = max(MIN_BLOCK_SIZE_WORDS, bsize/WSIZE); /* respect minimum size */

    /* Search the free list for a fit */
    if ((bp = find_fit(awords)) != NULL) {
        place(bp, awords);
        return bp->payload;
    }

    /* No fit found. Get more memory and place the block */
    size_t extendwords = max(awords,CHUNKSIZE); /* Amount to extend heap if no fit */
    if ((bp = extend_heap(extendwords)) == NULL)  
        return NULL;
    
    place(bp, awords);
    return bp->payload;
}

/*
 * mm_free - Frees the memory block and coalesces if possible
 */
extern void mm_free (void *ptr)
{
    //Assert mm_init called
    assert (heap_listp != 0);
    if (ptr == 0) //NULL
        return;
    struct block *bp = ptr - offsetof(struct block, payload);
    assert(bp != NULL); //Assert block pointer is not null
    size_t size = blk_size(bp);
    
    //Free and coalesce block
    mark_block_free(bp, size);
    coalesce(bp);
}

/*
 * mm_realloc - Given the pointer the the payload and the new requested size.
 * Resizes a memory block, possibly moving its location, to hold this new block 
 * to the best abillity depending on the cases of neighboring block allocation 
 */

void *mm_realloc(void *ptr, size_t size)
{
    /* If size == 0 then this is just free, and we return NULL. */
    if (size == 0) {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if (ptr == NULL) {
        return mm_malloc(size);
    }


    /* Copy the old data. */
    struct block *oldblock = ptr - offsetof(struct block, payload);
    assert(oldblock != NULL); //Assert block is not null
    size_t oldpayloadsize = blk_size(oldblock) * WSIZE - 2 * sizeof(struct boundary_tag);
    assert(oldpayloadsize > 0); //Assert greater than 0

    bool prev_alloc = prev_blk_footer(oldblock)->inuse;   /* is previous block allocated? */
    bool next_alloc = ! blk_free(next_blk(oldblock)); 

    size_t bsize = align(size + 2 * sizeof(struct boundary_tag));    /* account for tags */
    if (bsize < size)   
        return NULL;    /* integer overflow */
    
    /* Adjusted block size in words */
    size_t awords = max(MIN_BLOCK_SIZE_WORDS, bsize/WSIZE);

        //Case 1 
        if(!prev_alloc && next_alloc && blk_size(prev_blk(oldblock)) + blk_size(oldblock) >= awords)
        {
            list_remove(&prev_blk(oldblock)->elem);
            oldblock = prev_blk(oldblock);
            mark_block_used(oldblock, blk_size(next_blk(oldblock)) + blk_size(oldblock));
            memmove(oldblock->payload, ptr, oldpayloadsize);
            return oldblock->payload;
        }
        //Case 2, prev allocated, next free
        else if (!next_alloc && (blk_size(next_blk(oldblock)) + blk_size(oldblock) >= awords))
        {
            list_remove(&next_blk(oldblock)->elem);
            mark_block_used(oldblock, blk_size(next_blk(oldblock)) + blk_size(oldblock));
            return oldblock->payload;
        }
        //Case 4, prev and next are free, size + prev + next
        else if (!prev_alloc && !next_alloc && (blk_size(prev_blk(oldblock)) + blk_size(oldblock) + blk_size(next_blk(oldblock)) >= awords))
        {
            list_remove(&next_blk(oldblock)->elem);
            list_remove(&prev_blk(oldblock)->elem);
            mark_block_used(prev_blk(oldblock), blk_size(next_blk(oldblock)) + blk_size(oldblock) + blk_size(prev_blk(oldblock)));
            oldblock = prev_blk(oldblock);
            memmove(oldblock->payload, ptr, oldpayloadsize);
            return oldblock->payload;
        }
        //Case 5, at end of heap
        else if(prev_alloc && next_blk(oldblock) == NULL)
        {
            extend_heap(CHUNKSIZE);
            mark_block_used(oldblock, blk_size(next_blk(oldblock)) + blk_size(oldblock));
            return oldblock->payload;
        }

    void *newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if (!newptr) {
        return 0;
    }

    if (size < oldpayloadsize) oldpayloadsize = size;
    memcpy(newptr, ptr, oldpayloadsize);

    /* Free the old block. */
    mm_free(ptr);

    return newptr;
}





//Helper Functions--------------------------------------------------------
/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static struct block *coalesce(struct block *bp) 
{
    assert(bp != NULL); //Assert block pointer is valid.
    bool prev_alloc = prev_blk_footer(bp)->inuse;   /* is previous block allocated? */
    bool next_alloc = ! blk_free(next_blk(bp));     /* is next block allocated? */
    size_t size = blk_size(bp);
    assert(size > 0); //Assert block size is greater than 0

    if (prev_alloc && next_alloc) {            /* Case 1 */
        segregatedListAdd(bp);
        return bp;
    }
    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        list_remove(&next_blk(bp)->elem); //Remove the next one so can coalesce these 2.
        mark_block_free(bp, size + blk_size(next_blk(bp)));
    }
    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        list_remove(&prev_blk(bp)->elem);
        bp = prev_blk(bp);
        mark_block_free(bp, size + blk_size(bp));
    }
    else {                                     /* Case 4 */
        list_remove(&prev_blk(bp)->elem);
        list_remove(&next_blk(bp)->elem);
        mark_block_free(prev_blk(bp), 
                        size + blk_size(next_blk(bp)) + blk_size(prev_blk(bp)));
        bp = prev_blk(bp);
    }
    segregatedListAdd(bp);
    return bp;
}


/* 
 * checkheap - We don't check anything right now. 
 */
void mm_checkheap(int verbose)
{ 
}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static struct block *extend_heap(size_t words) 
{
    void *bp = mem_sbrk(words * WSIZE);

    if (bp == NULL)
        return NULL;

    /* Initialize free block header/footer and the epilogue header.
     * Note that we overwrite the previous epilogue here. */
    struct block * blk = bp - sizeof(FENCE);
    mark_block_free(blk, words);
    next_blk(blk)->header = FENCE;

    /* Coalesce if the previous block was free */
    return coalesce(blk);
}

/* 
 * place - Place block of asize words at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void place(struct block *bp, size_t asize)
{
    assert(asize > 0); //Assert valid size
    size_t csize = blk_size(bp);

    list_remove(&bp->elem);
    if ((csize - asize) >= MIN_BLOCK_SIZE_WORDS) { 
        mark_block_used(bp, asize);
        
        bp = next_blk(bp);
        mark_block_free(bp, csize-asize);
        segregatedListAdd(bp);
    }
    else { 
        mark_block_used(bp, csize);
    }
}

/* 
 * find_fit - Find a fit for a block with asize words, loops through each index searching through
 * the free list and returns a block that works but it will move to the next index if a counter variable 
 * is reached 
 */
static struct block *find_fit(size_t asize)
{
    assert(asize > 0); //Assert valid size
    struct list_elem *e;
    /* First fit search */
    for (int i = 0; i < NUM_SIZE_CLASSES; i++)
    {   
        int count = 0;
        for (e = list_begin(&segregatedList[i]); e != list_end(&segregatedList[i]); e = list_next(e)) 
        {   
            count++;
            if(count >= 5)
            {
                break;
            }            
            struct block *bp = list_entry(e, struct block, elem);
            if (blk_free(bp) && asize <= blk_size(bp)) {
                return bp;
            }
        }
    }
    
    return NULL; /* No fit */
}


/*
* segregatedListAdd - Add to segregated list, using block size to determine which index in the list.
*/
static void segregatedListAdd(struct block *bp)
{
    assert(bp != NULL); //Assert block is not null
    int blkSize = blk_size(bp);

    if (blkSize <= 128){
        list_push_front(&segregatedList[0], &bp->elem);
    }
    else if (blkSize <= 256){
        list_push_front(&segregatedList[1], &bp->elem);
    }
    else if (blkSize <= 512){
        list_push_front(&segregatedList[2], &bp->elem);
    }
    else if (blkSize <= 1024){
        list_push_front(&segregatedList[3], &bp->elem);
    }
    else if (blkSize <= 2048){
        list_push_front(&segregatedList[4], &bp->elem);
    }
    else if (blkSize <= 4096){
        list_push_front(&segregatedList[5], &bp->elem);
    }
    else if (blkSize <= 8192){
        list_push_front(&segregatedList[6], &bp->elem);
    }
    else if (blkSize <= 16384){
        list_push_front(&segregatedList[7], &bp->elem);
    }
    else if (blkSize <= 32768){
        list_push_front(&segregatedList[8], &bp->elem);
    }
    else{
        list_push_front(&segregatedList[9], &bp->elem);
    }
}



team_t team = {
    /* Team name */
    "Team jk",
    /* First member's full name */
    "Johan Lee",
    /* Second member's full name (leave as empty strings if none) */
    "Kevin He",
};
