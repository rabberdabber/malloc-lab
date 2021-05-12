

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"


/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/


/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<10)

/*segregated list size*/
#define LST_COUNT 28

#define MAX(x, y) ((x) > (y)? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

/* get the word at address p*/
#define GET(p) (*(unsigned int *)(p))
/* write a val to the word at address p*/
#define PUT(p,val) (*(unsigned int *)(p) = (val))
/*write an address to the ptr p*/
#define PUTADDR(p,addr) (*(unsigned int*)(p) = (unsigned int)(addr))

/*get the size from the header or the footer p*/
#define GET_SIZE(p)  (GET(p) & ~0x7)
/*get allocation status from header or footer p*/
#define GET_ALLOC(p) (GET(p) & 0x1)

/* header address of bp where bp is the payload address*/ 
#define HDRP(bp) ((char *)(bp) - WSIZE)
/*footer address of bp  where bp is the payload address*/
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
/* given bp of the current block find the bp of the next block*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))
/* giben bp of the current block find the bp of the prev block*/
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

/*given a free chunk find next chunk's address(if it exists)*/
#define GET_NEXT(p) (*(char **)((char *)(p) + WSIZE))
/*given a free chunk find prev chunk's address(if it exists)*/
#define GET_PREV(p) (*(char **)(p))
/* given a ptr set its next_ptr(if it exists)*/
#define SET_NEXT(p,next) PUTADDR((char *)(p) + WSIZE,next)
/* given a ptr set its prev_ptr(if it exists)*/
#define SET_PREV(p,prev) PUTADDR(p,prev)
#define GET_INDEX(p)   (GET_SIZE(HDRP(p)))/(DSIZE)


/* function prototypes*/
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *search_chunk(size_t units);
static void remove_chunk(void *ptr);
static void insert_chunk(void *ptr);
static void *split_chunk(void *bp, size_t asize);
static int  map(size_t x);



void **seg_lst;


static int  map(size_t x){
 int mask,mask1,index,minus_one;
 // set all the bits to the right of the left most set bit to one
 x = x | (x >> 16);
 x = x | (x >> 8);
 x = x | (x >> 4);
 x = x | (x >> 2);
 x = x | (x >> 1);
 // then count the number of set bits
 minus_one = (~0x1) + 1;
 mask = 0X11 | (0X11 << 8) | (0X11 << 16) | (0X11 << 24);
 mask1 = 0X0f | (0X0f << 8) | (0X0f << 16) | (0X0f << 24);
 index = (x & mask) + ((x >> 1) & mask) + ((x >> 2) & mask) + ((x >> 3) & mask);
 index = (((index & mask1) + ((index >> 4) & mask1)) & mask1);
 return ((index + (index >> 8)  + (index >> 16)  + (index >> 24) + minus_one) & 0X3F);
}


static void *coalesce(void *bp){

   size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
   size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
   size_t size = GET_SIZE(HDRP(bp));
 
   /*case 1*/
   if(prev_alloc && next_alloc){
    }

   /*case 2*/
   else if (prev_alloc && !next_alloc) {
     remove_chunk(NEXT_BLKP(bp));
     size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
     PUT(HDRP(bp), PACK(size, 0));
     PUT(FTRP(bp), PACK(size, 0));
   }
   /*case 3*/
   else if (!prev_alloc && next_alloc) {
     remove_chunk(PREV_BLKP(bp));
     size += GET_SIZE(HDRP(PREV_BLKP(bp)));
     PUT(FTRP(bp), PACK(size, 0));
     PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
     bp = PREV_BLKP(bp);
   }
   /*case 4*/
   else {
     remove_chunk(NEXT_BLKP(bp)); 
     remove_chunk(PREV_BLKP(bp));
     size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
     GET_SIZE(FTRP(NEXT_BLKP(bp)));
     PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
     PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
     bp = PREV_BLKP(bp);
   }
   return bp;


 }

static void *extend_heap(size_t size){
    void *bp;                   
    //consider alignment
    size = ALIGN(size);

    if ((bp = mem_sbrk(size)) == (void *) -1)
        return NULL;
  
    // Set headers and footer 
    PUT(HDRP(bp), PACK(size, 0));  
    PUT(FTRP(bp), PACK(size, 0));   
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    bp = coalesce(bp);
    insert_chunk(bp);   
    return bp;;
}

static void *search_chunk(size_t size) {
 /* best-fit search */
 int index = map(size);//mapping of the block size and the index
 void *ptr;
 for(;index < LST_COUNT;index++){
   for (ptr = seg_lst[index];ptr; ptr = GET_NEXT(ptr))
      if(size <= GET_SIZE(HDRP(ptr))){;
        return ptr;
      }
 }

 return NULL; /* No fit */  
}



static void remove_chunk(void *ptr) {
 
   int index = map(GET_SIZE(HDRP(ptr)));

   void *nxt_ptr = GET_NEXT(ptr);
   void *prev_ptr = GET_PREV(ptr);

   if(prev_ptr)
    SET_NEXT(prev_ptr,nxt_ptr);
   
   if(nxt_ptr)
    SET_PREV(nxt_ptr,prev_ptr);

   if(!prev_ptr)
     seg_lst[index] = nxt_ptr;
   
   SET_NEXT(ptr,NULL);
   SET_PREV(ptr,NULL);

}

static void insert_chunk(void *ptr) {
  size_t size = GET_SIZE(HDRP(ptr));
  int index = map(size);
  /*insert LIFO in the seg_list*/
  void *first = seg_lst[index];
  if(first)
   SET_PREV(first,ptr);
  SET_NEXT(ptr,seg_lst[index]);
  SET_PREV(ptr,NULL);
  seg_lst[index] = ptr;
}

/* should try to split the block and return the requested block*/
/* and also insert the remaining chunk into the appropriate list*/
static void *split_chunk(void *bp, size_t asize) {

 size_t csize = GET_SIZE(HDRP(bp));
 remove_chunk(bp);
 void *ptr = bp;
 if ((csize - asize) >= (2*DSIZE)) {
  PUT(HDRP(bp), PACK(asize, 1));
  PUT(FTRP(bp), PACK(asize, 1));
  bp = NEXT_BLKP(bp);
  PUT(HDRP(bp), PACK(csize-asize, 0));
  PUT(FTRP(bp), PACK(csize-asize, 0));
  insert_chunk(bp);
 }
 else {
  PUT(HDRP(ptr), PACK(csize, 1));
  PUT(FTRP(ptr), PACK(csize, 1));
 }
 return ptr;
}

/* 
 * mm_init - initialize the malloc package.
 */

int mm_init(void)
{
  
  void *heap_listp = NULL;
  if((heap_listp = mem_sbrk(32*WSIZE)) == (void *)-1){
     return -1;
  }
  seg_lst = heap_listp;
  /*initializing the array that stores the segregated lists*/
  for(int i = 0;i < LST_COUNT;i++){
    seg_lst[i] = NULL;
  }

  PUT(&seg_lst[28], 0);                          /* Alignment padding */
  PUT(&seg_lst[29], PACK(DSIZE, 1)); /* Prologue header */
  PUT(&seg_lst[30], PACK(DSIZE, 1)); /* Prologue footer */
  PUT(&seg_lst[31], PACK(0, 1));     /* Epilogue header */
  if(extend_heap(CHUNKSIZE) == NULL)
    return -1;
  return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)

{ 
   
    size_t blk_size; /* Adjusted block size */
    size_t extendsize;/* Amount to extend heap if no fit*/
    void *bp;

    /* Ignore spurious requests */
    if(!size)
      return NULL;
    /*Adjust block size to include overhead and alignment reqs. */

    blk_size = ALIGN(size) + DSIZE;

    /* Search the segregated list for a fit */
    if((bp = search_chunk(blk_size)) != NULL){
     /*try splitting*/
     bp = split_chunk(bp,blk_size);
     return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(blk_size,CHUNKSIZE);
    if((bp = extend_heap(extendsize)) == NULL)
      return NULL;
    /*try splitting*/
    bp = split_chunk(bp,blk_size);
    return bp;
}


void mm_free(void *bp)
{

 size_t size = GET_SIZE(HDRP(bp));
 /* set them free */
 PUT(HDRP(bp),PACK(size,0));
 PUT(FTRP(bp),PACK(size,0));
 bp =  coalesce(bp);
 insert_chunk(bp);
}



/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{

    size_t blk_size = 0,nsize;
    size_t copySize = 0,cursize = 0;
    void *newptr = NULL;
    void *oldptr = ptr;
    void *nextptr = NULL;

    blk_size = ALIGN(size) + DSIZE;

   if(!ptr)
     return mm_malloc(blk_size);

    // if valid ptr
    nextptr = NEXT_BLKP(oldptr);
    cursize = GET_SIZE(HDRP(ptr));
    copySize = cursize -DSIZE;

   if(!size){
      mm_free(ptr);
      return NULL;
   }

   //if requested memory is too small
   else if (blk_size <=  cursize) {
      insert_chunk(ptr);
      return split_chunk(ptr,blk_size);
   }
   // if next chunk is available
   else  if (nextptr && !GET_ALLOC(HDRP(nextptr))) {
       nsize = GET_SIZE(HDRP(nextptr));
      if (nsize + GET_SIZE(HDRP(oldptr)) >= blk_size) {
        remove_chunk(nextptr);
        if (nsize + copySize  <= blk_size) {
          PUT(HDRP(oldptr), PACK(cursize + nsize, 1));
          PUT(FTRP(oldptr), PACK(cursize + nsize, 1));
          return oldptr;
        }
        else{
          PUT(HDRP(oldptr), PACK(blk_size, 1));
          PUT(FTRP(oldptr), PACK(blk_size, 1));
          newptr = oldptr;
          oldptr = NEXT_BLKP(newptr);
          PUT(HDRP(oldptr), PACK(cursize + nsize - blk_size, 0));
          PUT(FTRP(oldptr), PACK(cursize + nsize - blk_size, 0));
          oldptr =  coalesce(oldptr);
          insert_chunk(oldptr);
          return newptr;
        }
      }
    }
    //last resort
    newptr = mm_malloc(size);
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;

}


