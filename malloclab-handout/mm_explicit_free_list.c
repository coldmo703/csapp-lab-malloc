/*
    explicit free list ver. use a stack which contains a free blocks. 
    also, reallocation algorithm improved.
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
#define MIN_BLOCK_SIZE (2*DSIZE)
#define CHUNKSIZE mem_pagesize()
#define MAX(x, y) ((x) > (y)? (x) : (y))
#define ABS(x) ((x)>0 ? (x) : (-1)*(x))
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

//explicit free list. payload 내부에 후손, 자손 포인터를 wsize만큼 저장. 
#define PRED_FREE(bp) ((char *)(bp))
#define SUCC_FREE(bp) ((char *)(bp) + WSIZE)

#define GET_PRED(bp) (*(void **)(PRED_FREE(bp)))
#define GET_SUCC(bp) (*(void **)(SUCC_FREE(bp)))

#define SET_PRED(bp, ptr) (GET_PRED(bp) = (ptr))
#define SET_SUCC(bp, ptr) (GET_SUCC(bp) = (ptr))

static void *heap_listp;
static void *stack_top;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void remove_block(void *bp);
static void insert_block(void *bp);
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) return -1;
    stack_top=NULL;
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

    if(size<=MIN_BLOCK_SIZE-DSIZE) asize=MIN_BLOCK_SIZE;
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
    void *bp;
    void *best_bp=NULL;
    size_t min_diff = (size_t)-1;
    int cnt=0;
    for(bp=stack_top; bp!=NULL; bp=GET_PRED(bp)){
        size_t bsize = GET_SIZE(HDRP(bp));
        if(bsize>=asize){
            size_t diff = bsize - asize;
            if(diff==0) return bp;
            if(diff<min_diff){
                min_diff=diff;
                best_bp=bp;
            }
        }
        cnt++;
        if(cnt>10000) break;
    }
    return best_bp;
}

static void place(void *bp, size_t asize){
    size_t csize=GET_SIZE(HDRP(bp));

    if((csize-asize)>=MIN_BLOCK_SIZE){
        remove_block(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp=NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        coalesce(bp);
        
    }
    else{
        remove_block(bp);
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
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* Case 2: 뒤 블록만 free */
    if (prev_alloc && !next_alloc) {
        remove_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    /* Case 3: 앞 블록만 free */
    else if (!prev_alloc && next_alloc) {
        remove_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    /* Case 4: 앞뒤 모두 free */
    else if (!prev_alloc && !next_alloc) {
        remove_block(PREV_BLKP(bp));
        remove_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    /* 새로 만들어진 (또는 병합된) 가용 블록을 리스트에 삽입 */
    insert_block(bp);
    return bp;
}


static void remove_block(void *bp) {
    if (bp == NULL) return;

    void *prev = GET_PRED(bp);
    void *next = GET_SUCC(bp);

    /* 1. 이전 노드의 SUCC 포인터 갱신 */
    if (prev != NULL) {
        SET_SUCC(prev, next);
    }

    /* 2. 다음 노드의 PRED 포인터 또는 Top 포인터(free_listp) 갱신 */
    if (next != NULL) {
        SET_PRED(next, prev);
    } else {
        /* next가 NULL이라는 것은 bp가 스택의 맨 끝(Top)이었다는 의미 */
        stack_top = prev;
    }
}

static void insert_block(void *bp) {
    if (bp == NULL) return;

    /* 새 블록은 Top이 되므로 다음(SUCC)은 NULL */
    SET_SUCC(bp, NULL);
    SET_PRED(bp, stack_top);

    if (stack_top != NULL) {
        /* 기존 Top의 다음으로 새 블록 연결 */
        SET_SUCC(stack_top, bp);
    }
    
    /* Top 포인터를 새 블록으로 갱신 */
    stack_top = bp;
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (size == 0) {
        if (ptr != NULL) {
            mm_free(ptr);
        }
        return NULL;
    }
    if (ptr == NULL) {
        return mm_malloc(size);
    }

    /* 1. 요청 크기 정렬: 최소 블록 크기 보장 및 8바이트 정렬 */
    size_t asize;
    if (size <= DSIZE) {
        asize = MIN_BLOCK_SIZE;
    } else {
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
    }

    size_t origin_size = GET_SIZE(HDRP(ptr));
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t prev_size = GET_SIZE(HDRP(PREV_BLKP(ptr)));
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));

    /* 2. 블록 축소/유지: Split하지 않고 그대로 반환 (단편화 방지 핵심) */
    if (asize <= origin_size) {
        return ptr;
    }

    /* 3. 블록 확대 분기 */

    /* Case 1: 오른쪽 블록만 free인 경우 */
    if (prev_alloc && !next_alloc) {
        if (origin_size + next_size >= asize) {
            remove_block(NEXT_BLKP(ptr));
            size_t total_size = origin_size + next_size;

            /* 자투리가 분할할 만큼 남을 때만 쪼갬 */
            if (total_size - asize >= MIN_BLOCK_SIZE) {
                PUT(HDRP(ptr), PACK(asize, 1));
                PUT(FTRP(ptr), PACK(asize, 1));
                void *split_bp = NEXT_BLKP(ptr);
                PUT(HDRP(split_bp), PACK(total_size - asize, 0));
                PUT(FTRP(split_bp), PACK(total_size - asize, 0));
                insert_block(split_bp);
            } else {
                PUT(HDRP(ptr), PACK(total_size, 1));
                PUT(FTRP(ptr), PACK(total_size, 1));
            }
            return ptr;
        }
    }
    /* Case 2: 왼쪽 블록만 free인 경우 */
    else if (!prev_alloc && next_alloc) {
        if (origin_size + prev_size >= asize) {
            void *prevptr = PREV_BLKP(ptr);
            remove_block(prevptr);
            size_t total_size = origin_size + prev_size;

            memmove(prevptr, ptr, origin_size - DSIZE);

            if (total_size - asize >= MIN_BLOCK_SIZE) {
                PUT(HDRP(prevptr), PACK(asize, 1));
                PUT(FTRP(prevptr), PACK(asize, 1));
                void *split_bp = NEXT_BLKP(prevptr);
                PUT(HDRP(split_bp), PACK(total_size - asize, 0));
                PUT(FTRP(split_bp), PACK(total_size - asize, 0));
                insert_block(split_bp);
            } else {
                PUT(HDRP(prevptr), PACK(total_size, 1));
                PUT(FTRP(prevptr), PACK(total_size, 1));
            }
            return prevptr;
        }
    }
    /* Case 3: 양쪽 모두 free인 경우 */
    else if (!prev_alloc && !next_alloc) {
        if (origin_size + prev_size + next_size >= asize) {
            void *prevptr = PREV_BLKP(ptr);
            remove_block(prevptr);
            remove_block(NEXT_BLKP(ptr));
            size_t total_size = origin_size + prev_size + next_size;

            memmove(prevptr, ptr, origin_size - DSIZE);

            if (total_size - asize >= MIN_BLOCK_SIZE) {
                PUT(HDRP(prevptr), PACK(asize, 1));
                PUT(FTRP(prevptr), PACK(asize, 1));
                void *split_bp = NEXT_BLKP(prevptr);
                PUT(HDRP(split_bp), PACK(total_size - asize, 0));
                PUT(FTRP(split_bp), PACK(total_size - asize, 0));
                insert_block(split_bp);
            } else {
                PUT(HDRP(prevptr), PACK(total_size, 1));
                PUT(FTRP(prevptr), PACK(total_size, 1));
            }
            return prevptr;
        }
    }

    /* Case 4: 양쪽 다 alloc이거나, 합쳐도 크기가 부족한 경우 -> 새로 할당 */
    void *newptr = mm_malloc(size);
    if (newptr == NULL) {
        return NULL;
    }
    memcpy(newptr, ptr, origin_size - DSIZE);
    mm_free(ptr);
    return newptr;
}