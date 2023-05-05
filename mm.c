/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  Blocks are never coalesced or reused.  The size of
 * a block is found at the first aligned word before the block (we need
 * it for realloc).
 *
 * This code is correct and blazingly fast, but very bad usage-wise since
 * it never frees anything.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */
static char *free_list_head= NULL;
static char *heap_listp;
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

#define MAXM 2
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))


#define WSIZE 4            /* 字的大小 Word and header/footer size (bytes) */
#define DSIZE 8            /* 双字的大小 Double word size (bytes) */
#define CHUNKSIZE (1 << 12)  /* 初始空闲块的大小和扩展堆时的默认大小 extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* pack a size and allocated bit into a word   将大小和分配的位打包到一个字中*/
#define PACK(size, alloc)   ((size) | (alloc)) 

/* read and write a word at address p */
#define GET(ptr) (*(unsigned int *)(ptr))
#define PUT(ptr, val) ((*(unsigned int *)(ptr)) = (unsigned int)(val))     

/* read the size and allocated fields from address p */
/* 0 -> unalloca, 1 -> alloca */
#define GET_SIZE(ptr) (GET(ptr) & ~0x7) 
#define GET_ALLOC(ptr) (GET(ptr) & 0x1) 

/* given block ptr, compute address of its header and footer*/
#define HDRP(ptr)  ((char *)(ptr)-WSIZE) 
#define FTRP(ptr)  ((char *)(ptr)+GET_SIZE(HDRP(ptr))-DSIZE) 

/* given block ptr, get next or previous block ptr */
#define NEXT_BLKP(ptr) ((char *)(ptr) + GET_SIZE(((char *)(ptr)-WSIZE))) 
#define PREV_BLKP(ptr) ((char *)(ptr) - GET_SIZE(((char *)(ptr)-DSIZE))) 

#define GET_PREV_FREEBLKP(ptr)   ((GET((char *)(ptr))) == 0 ? NULL : ((int *)((long)(GET((char *)(ptr))) + (long)(heap_listp)))) 
#define GET_NEXT_FREEBLKP(ptr)   ((GET((char *)(ptr) + WSIZE)) == 0 ? NULL : ((int *)((long)(GET((char *)(ptr) + WSIZE)) + (long)(heap_listp)))) 

#define SET_PREV_FREEBLKP(ptr, val)   (val == 0 ? (PUT(((char *)(ptr)), (val))) : (PUT(((char *)(ptr)), (val - (long)(heap_listp))))) 
#define SET_NEXT_FREEBLKP(ptr, val)   (val == 0 ? (PUT(((char *)(ptr) + WSIZE), (val))) : (PUT(((char *)(ptr) + WSIZE), (val - (long)(heap_listp))))) 

static void insert_free_block(void *ptr) {
  if (ptr == NULL || GET_ALLOC(HDRP(ptr)) == 1) { return; }
  //插入第一个值 
  if (free_list_head == NULL) {
    free_list_head = ptr;                           
    SET_PREV_FREEBLKP(ptr, 0);
    SET_NEXT_FREEBLKP(ptr, 0);
    return;
  }
  //嵌入链表
  SET_PREV_FREEBLKP(ptr, 0);
  SET_NEXT_FREEBLKP(ptr, (long)free_list_head);
  SET_PREV_FREEBLKP(free_list_head, (long)ptr);
  free_list_head = ptr;
}

static void remove_free_block(void *ptr) {
  if (ptr==NULL || GET_ALLOC(HDRP(ptr))==1) return;
  void *prev_freeblkp=GET_PREV_FREEBLKP(ptr);
  void *next_freeblkp=GET_NEXT_FREEBLKP(ptr);
  if (prev_freeblkp == NULL && next_freeblkp == NULL) { free_list_head=NULL; } 
  else if (prev_freeblkp==NULL) { free_list_head=next_freeblkp; SET_PREV_FREEBLKP(next_freeblkp, 0); } 
  else if (next_freeblkp==NULL) { SET_NEXT_FREEBLKP(prev_freeblkp, 0); } 
  else {  SET_NEXT_FREEBLKP(prev_freeblkp, (long)next_freeblkp); SET_PREV_FREEBLKP(next_freeblkp, (long)prev_freeblkp);
  }
}

//void *mem_sbrk(int incr)：将堆增大 incr 字节，其中 incr 是一个非零的正整数，并返回一个通用指针指向新分配的堆区域的首个字节。
static void *coalesce(void *ptr) {
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
  size_t size = GET_SIZE(HDRP(ptr));

  if (prev_alloc && next_alloc) {
    insert_free_block(ptr);
    return ptr;
  } else if (prev_alloc && !next_alloc) {
    remove_free_block(NEXT_BLKP(ptr));
    size+=GET_SIZE(HDRP(NEXT_BLKP(ptr)));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
  } else if (!prev_alloc && next_alloc) {
    remove_free_block(PREV_BLKP(ptr));
    size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
    PUT(FTRP(ptr), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
    ptr = PREV_BLKP(ptr);
  } else {
    remove_free_block(PREV_BLKP(ptr));
    remove_free_block(NEXT_BLKP(ptr));
    size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
    PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
    ptr = PREV_BLKP(ptr);
  }
  insert_free_block(ptr);
  return ptr;
}



static void place(void *ptr, size_t need_size) {
  size_t exist_size = GET_SIZE(HDRP(ptr));
  remove_free_block(ptr);
  // 如果多余块大小小于2byte 就把他当做碎片 否则拆分
  if (exist_size - need_size > DSIZE) {
    PUT(HDRP(ptr), PACK(need_size,1));
    PUT(FTRP(ptr), PACK(need_size,1));
    ptr = NEXT_BLKP(ptr);
    PUT(HDRP(ptr), PACK(exist_size-need_size, 0));
    PUT(FTRP(ptr), PACK(exist_size-need_size, 0));
    coalesce(ptr);
  } else {
    PUT(HDRP(ptr), PACK(exist_size, 1));
    PUT(FTRP(ptr), PACK(exist_size, 1));
  }
}

static void *find_fit(size_t need_size) {
  char  *ptr = NULL;
  size_t mn=0; 
  size_t tot=0;
  for (void  *i=free_list_head; i!=NULL; i=GET_NEXT_FREEBLKP(i),tot++) {
    if (GET_SIZE(HDRP(i))>=need_size) {if (GET_SIZE(HDRP(i))<=mn || mn==0) { ptr=i; mn=GET_SIZE(HDRP(i)); } }
    if (tot>MAXM && ptr != NULL) break;
  }
  return ptr; 
}

static void *extend_heap(size_t words) {
  char *ptr;
  //size_t size;

  /*allocate an even number of words to maintain alignment*/
  //size= (words%2)? (words+1)*WSIZE : words*WSIZE;
  if ((long)(ptr = mem_sbrk(words)) == -1) return NULL;
  /*之前的结束块被当作新的块的头了,头上存这个块的size和alloc,头不是char* ptr 而是 char* ptr-WSIZE*/
  PUT(HDRP(ptr), PACK(words, 0));
  PUT(FTRP(ptr), PACK(words, 0));
  PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));

  /*合并Coalesce if the previous block was free*/
  return coalesce(ptr);
}


// 填充字+序言块+分配块/空闲块+结束块
int mm_init(void){
  if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) // 从内存系统中得到四个字
    return -1;  
  // create the initial empty heap 将它们初始化 创建一个空的空闲链表
  //heaplistp总是指向序言块（作为一个小优化，我们可以让它指向下一个块）
  PUT(heap_listp, 0);//双字边界对齐的不使用的填充字 alignment padding
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); //序言块头部prologue header
  PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); //序言块尾部prologue footer
  PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     //结束块 结束块是一个大小为0的已分配块Epilogue header
  heap_listp += 2*WSIZE;                                                     
  free_list_head = NULL;

  // extend the empty heap with a free block of CHUNKSIZE bytes 创建初始的空闲块
  if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
    return -1;
  return 0;
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size){
  size_t asize;//Adjusted block size 
  size_t extendsize;//Amount to extend heap if no fit
  char *ptr;
  /* Ignore spurious requests */
  if (size == 0) {
    return NULL;
  }

  /*Adjust block size to include overhead and alignment reqs*/
  asize = ALIGN(size + DSIZE);

  /*Search the free list for a fit*/
  if ((ptr = find_fit(asize)) != NULL) {
    place(ptr, asize);
    return ptr;
  }

  /*No fit found.Get more memory and place the block */
  extendsize = MAX(asize, CHUNKSIZE/WSIZE);
  if ((ptr = extend_heap(extendsize)) == NULL) {
    return NULL;
  }
  place(ptr, asize);
  return ptr;
}

/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
void free(void *ptr){
	/*Get gcc to be quiet */
	if (ptr == NULL) return;
  size_t size = GET_SIZE(HDRP(ptr));

  PUT(HDRP(ptr), PACK(size, 0));
  PUT(FTRP(ptr), PACK(size, 0));
  coalesce(ptr);
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.  I'm too lazy
 *      to do better.
 */
void *realloc(void *oldptr, size_t size)
{
  size_t oldsize;
  void *newptr;

  /* If size == 0 then this is just free, and we return NULL. */
  if(size == 0) {
    free(oldptr);
    return 0;
  }

  /* If oldptr is NULL, then this is just malloc. */
  if(oldptr == NULL) {
    return malloc(size);
  }

  newptr = malloc(size);
  size_t SZ=GET_SIZE(HDRP(newptr));
  /* If realloc() fails the original block is left untouched  */
  if(!newptr) {
    return 0;
  }

  /* Copy the old data. */
  oldsize =  GET_SIZE(HDRP(oldptr));
  if(oldsize<SZ) SZ=oldsize;
  memcpy(newptr, oldptr, SZ-DSIZE);

  /* Free the old block. */
  free(oldptr);

  return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
*/
void *calloc (size_t nmemb, size_t size)
{
  size_t bytes = nmemb * size;
  void *newptr;

  newptr = malloc(bytes);
  memset(newptr, 0, bytes);

  return newptr;
}

/*
 * mm_checkheap - There are no bugs in my code, so I don't need to check,
 *      so nah!
 */
void mm_checkheap(int verbose){
	/*Get gcc to be quiet. */
  verbose = verbose;
  
  //检查堆
  //检查epilogue and prologue blocks
  if (GET_SIZE(HDRP(heap_listp)) != DSIZE || GET_ALLOC(HDRP(heap_listp))!=1 || GET_SIZE(FTRP(heap_listp)) != DSIZE || GET_ALLOC(FTRP(heap_listp))!=1) { printf("Prologue block error\n"); assert(0);}
  //检查块的地址排列Check the address arrangement of the block
  char *ptr;
  ptr = heap_listp; while (GET_SIZE(HDRP(ptr))!=0) { ptr = NEXT_BLKP(ptr);}
  if (GET_SIZE(HDRP(ptr))!= 0 || GET_ALLOC(HDRP(ptr))!=1) { printf("Epilogue block error\n"); }
  //检查堆的边界 void *mem_heap_lo(void)：返回一个指向堆中第一个字节的通用指针。 void *mem_heap_hi(void)：返回一个指向堆中最后一个字节的通用指针。
  if (mem_heap_lo() + DSIZE != heap_listp) { printf("Left boundary of heap error\n");}
  if (mem_heap_hi() + 1 != (void *)ptr)   { printf("Right boundary of heap error\n");assert(0); }
  //检查每个区块的header和footer
  ptr=heap_listp;
  while (GET_SIZE(HDRP(ptr)) != 0) {
    //对齐
    if (GET_SIZE(HDRP(ptr)) < WSIZE)  {printf("Block size error\n"); assert(0);}
    if ((unsigned long long)ptr % DSIZE != 0) {printf("Alignment error\n"); assert(0);}
    //一致性
    if (ptr + GET_SIZE(HDRP(ptr)) != NEXT_BLKP(ptr)) { printf("Heap continuous error\n"); assert(0); }
    if (ptr != heap_listp) { if (FTRP(PREV_BLKP(ptr)) != ptr-DSIZE) printf("Heap continuous error\n");assert(0); }
    if (PREV_BLKP(NEXT_BLKP(ptr)) != ptr) { printf("Heap continuous error\n"); assert(0); }
    //header 和 footer 相互匹配
    if (GET_SIZE(HDRP(ptr)) != GET_SIZE(FTRP(ptr)) || (GET_ALLOC(HDRP(ptr)) != GET_ALLOC(FTRP(ptr)))) { printf("Header and footer are not consistent\n"); assert(0); }
    ptr=NEXT_BLKP(ptr);
  }
  //检查合并：堆中没有两个连续的空闲块
  ptr = heap_listp;
  while (GET_SIZE(HDRP(ptr))!=0) { ptr=NEXT_BLKP(ptr); if (GET_ALLOC(HDRP(ptr)) == 0 && GET_ALLOC(HDRP(NEXT_BLKP(ptr))) == 0) {printf("Merge error\n"); } }

  //检查空闲链表
  ptr=free_list_head;
  while (ptr != NULL) {
    //所有的后继/前驱指针是一致的（如果A的后继指针指向B,B的前驱指针应该指向A）
    if (GET_PREV_FREEBLKP(ptr) != NULL && (char *)GET_NEXT_FREEBLKP(GET_PREV_FREEBLKP(ptr))!=ptr) {printf("Prev and next error\n");} 
    ptr = (char *)GET_NEXT_FREEBLKP(ptr);
  }
  ptr=free_list_head;
  while (ptr != NULL) {
    //所有的空闲链表指针都指向 mem_heap_lo() 和 mem_heap_high() 之间。
    if (!((char *)mem_heap_lo() < ptr && ptr < (char *)mem_heap_hi())) { printf("Free list pointer error\n");} 
     ptr = (char *)GET_NEXT_FREEBLKP(ptr);
  }
  ptr=free_list_head;
  while (ptr != NULL) {
    if (GET_ALLOC(HDRP(ptr)) != 0) printf("Allocated block in the free list at %p\n", ptr);
    ptr = (char *)GET_NEXT_FREEBLKP(ptr);
  }
  ptr=free_list_head;
  while (ptr != NULL) {
  void *tmp = heap_listp;
    while (GET_SIZE(HDRP(ptr)) != 0) { if (tmp == ptr) break;  if (GET_SIZE(HDRP(tmp)) == 0) printf("Block in free list is not in the heap\n"); tmp = NEXT_BLKP(tmp); }
    ptr = (char *)GET_NEXT_FREEBLKP(ptr);
  }
}
