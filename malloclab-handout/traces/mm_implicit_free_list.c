/*
implicit free list 버전으로 작성한 csapp의 코드. 
 */
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
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE mem_pagesize()
#define MAX(x, y) ((x) > (y)? (x) : (y))
#define PACK(size, alloc)  ((size) | (alloc))
// Read and write a word at address p... unsigned int로 캐스팅하고 읽어오는것.
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
//header는 wordsize의 미니블록이고, 32비트에서 29비트는 블록사이즈를, 하위 3비트는 allocated 혹은 free 상태를 나타낸다.
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

//given block ptr bp, compute address of its header.
#define HDRP(bp) ((char *)(bp) - WSIZE)
//given block ptr bp, compute address of its footer.
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static char *heap_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) return -1;
    PUT(heap_listp, 0); //일단 워드 4개만큼 힙 확장. 그리고 정렬을 이유로 한 워드 비워놓는다. 
    //그리고 그 다음에 프롤로그 헤더, 프롤로그 푸터를 설치. 마지막 워드에는 에필로그헤더를 설치.
    PUT(heap_listp + (WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + 2*(WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp+ 3*(WSIZE), PACK(0,1));
    heap_listp+=(2*WSIZE);
    // heap_listp는 이제 프롤로그 블록을 항상 가리키는 고정 변수 역할을 할것이다. 
    if(extend_heap(CHUNKSIZE/WSIZE)==NULL) return -1;

    return 0;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;
    // 짝수개의 word를 할당할것이다. 
    size=(words%2) ? (words+1)*WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size))== -1){
        return NULL;
    }
    //기존의 에필로그 헤더를 새로운 하나의 거대한 free block의 헤더로 변환.
    PUT(HDRP(bp), PACK(size, 0));
    //그 다음 푸터도 추가해주고, 마지막엔 새로운 에필로그 헤더를 설치한다. 
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

    return coalesce(bp);
}
/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size==0) return NULL;

    if(size<=DSIZE) asize=2*DSIZE;
    else asize=DSIZE*((size+(DSIZE)+(DSIZE-1)) / DSIZE);

    // free list search. 
    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    // 만약 딱 맞는 free block을 찾지 못했다면, 힙을 연장시킨다.
    extendsize=MAX(asize, CHUNKSIZE);
    if((bp=extend_heap(extendsize/WSIZE))==NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize){
    char *ptr = heap_listp; // 프롤로그 블록

    // ptr 자체의 크기가 0(에필로그)보다 큰 동안만 전진
    while (GET_SIZE(HDRP(ptr)) > 0) {
        if (!GET_ALLOC(HDRP(ptr)) && (GET_SIZE(HDRP(ptr)) >= asize)) {
            return ptr;
        }
        ptr = NEXT_BLKP(ptr);
    }
    return NULL;
}

static void place(void *bp, size_t asize){
    size_t csize=GET_SIZE(HDRP(bp));

    if((csize-asize)>=(2*DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp=NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

static void *coalesce(void *bp){
    size_t prev_alloc=GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc=GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size=GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){
        return bp;
    }

    else if(prev_alloc && !next_alloc){
        size+=GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if(!prev_alloc && next_alloc){
        size+=GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp=PREV_BLKP(bp);
    }
    else{
        size+=GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp=PREV_BLKP(bp);
    }
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) {
        return mm_malloc(size);
    }
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    void *new_ptr = mm_malloc(size);
    if (new_ptr == NULL)
        return NULL;

    /* 기존 블록 크기 확인 (WSIZE/DSIZE 매크로 기준) */
    size_t copy_size = GET_SIZE(HDRP(ptr)) - DSIZE;
    if (size < copy_size)
        copy_size = size;

    memcpy(new_ptr, ptr, copy_size);
    mm_free(ptr);
    return new_ptr;
}














