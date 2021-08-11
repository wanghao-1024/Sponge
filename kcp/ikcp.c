//=====================================================================
//
// KCP - A Better ARQ Protocol Implementation
// skywind3000 (at) gmail.com, 2010-2011
//
// Features:
// + Average RTT reduce 30% - 40% vs traditional ARQ like tcp.
// + Maximum RTT reduce three times vs tcp.
// + Lightweight, distributed as a single source file.
//
//=====================================================================
#include "ikcp.h"

#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <stdio.h>

/*

0                 4      5   6        8 (BYTE)
-----------------+---+---+--------+ 
|      conv                  |cmd |frg   | wnd    | 
+----------------+----------------+ 8
|      ts        |      sn        | 
+----------------+----------------+ 16
|      una       |      len       |
+----------------+----------------+ 24
|                                 |
|            DATA (optional)      |
|                                 |
+---------------------------------+

// 头部共24字节
conv:4字节，连接号
cmd:1字节
frg:1字节，分片数量，用户数据可能会被分成多个KCP包发送出去
wnd:2字节，接受窗口大小，发送方的发送窗口不能超过接收方给出的数值
ts:4字节，时间戳，timestamp
sn:4字节，序列号
una:4字节，下一个可以接收的序列号，也就是确认号。例如收到sn=10的包，una就是11
len:4字节，用户数据长度
*/

//=====================================================================
// KCP BASIC
//=====================================================================
const IUINT32 IKCP_RTO_NDL = 30;        // no delay min rto
const IUINT32 IKCP_RTO_MIN = 100;       // normal min rto
const IUINT32 IKCP_RTO_DEF = 200;
const IUINT32 IKCP_RTO_MAX = 60000;
const IUINT32 IKCP_CMD_PUSH = 81;       // cmd: push data
const IUINT32 IKCP_CMD_ACK  = 82;       // cmd: ack
const IUINT32 IKCP_CMD_WASK = 83;       // cmd: window probe (ask)
const IUINT32 IKCP_CMD_WINS = 84;       // cmd: window size (tell)
const IUINT32 IKCP_ASK_SEND = 1;        // need to send IKCP_CMD_WASK
const IUINT32 IKCP_ASK_TELL = 2;        // need to send IKCP_CMD_WINS
const IUINT32 IKCP_WND_SND = 32;
const IUINT32 IKCP_WND_RCV = 32;
const IUINT32 IKCP_MTU_DEF = 1400;
const IUINT32 IKCP_ACK_FAST = 3;
const IUINT32 IKCP_INTERVAL = 100;
const IUINT32 IKCP_OVERHEAD = 24;
const IUINT32 IKCP_DEADLINK = 20;
const IUINT32 IKCP_THRESH_INIT = 2;
const IUINT32 IKCP_THRESH_MIN = 2;
const IUINT32 IKCP_PROBE_INIT = 7000;       // 7 secs to probe window size
const IUINT32 IKCP_PROBE_LIMIT = 120000;    // up to 120 secs to probe window


//---------------------------------------------------------------------
// encode / decode
//---------------------------------------------------------------------

/* encode 8 bits unsigned int */
static inline char *ikcp_encode8u(char *p, unsigned char c)
{
    *(unsigned char *)p++ = c;
    return p;
}

/* decode 8 bits unsigned int */
static inline const char *ikcp_decode8u(const char *p, unsigned char *c)
{
    *c = *(unsigned char *)p++;
    return p;
}

/* encode 16 bits unsigned int (lsb) */
static inline char *ikcp_encode16u(char *p, unsigned short w)
{
#if IWORDS_BIG_ENDIAN
    *(unsigned char *)(p + 0) = (w & 255);
    *(unsigned char *)(p + 1) = (w >> 8);
#else
    *(unsigned short *)(p) = w;
#endif
    p += 2;
    return p;
}

/* decode 16 bits unsigned int (lsb) */
static inline const char *ikcp_decode16u(const char *p, unsigned short *w)
{
#if IWORDS_BIG_ENDIAN
    *w = *(const unsigned char *)(p + 1);
    *w = *(const unsigned char *)(p + 0) + (*w << 8);
#else
    *w = *(const unsigned short *)p;
#endif
    p += 2;
    return p;
}

/* encode 32 bits unsigned int (lsb) */
static inline char *ikcp_encode32u(char *p, IUINT32 l)
{
#if IWORDS_BIG_ENDIAN
    *(unsigned char *)(p + 0) = (unsigned char)((l >>  0) & 0xff);
    *(unsigned char *)(p + 1) = (unsigned char)((l >>  8) & 0xff);
    *(unsigned char *)(p + 2) = (unsigned char)((l >> 16) & 0xff);
    *(unsigned char *)(p + 3) = (unsigned char)((l >> 24) & 0xff);
#else
    *(IUINT32 *)p = l;
#endif
    p += 4;
    return p;
}

/* decode 32 bits unsigned int (lsb) */
static inline const char *ikcp_decode32u(const char *p, IUINT32 *l)
{
#if IWORDS_BIG_ENDIAN
    *l = *(const unsigned char *)(p + 3);
    *l = *(const unsigned char *)(p + 2) + (*l << 8);
    *l = *(const unsigned char *)(p + 1) + (*l << 8);
    *l = *(const unsigned char *)(p + 0) + (*l << 8);
#else
    *l = *(const IUINT32 *)p;
#endif
    p += 4;
    return p;
}

static inline IUINT32 _imin_(IUINT32 a, IUINT32 b)
{
    return a <= b ? a : b;
}

static inline IUINT32 _imax_(IUINT32 a, IUINT32 b)
{
    return a >= b ? a : b;
}

static inline IUINT32 _ibound_(IUINT32 lower, IUINT32 middle, IUINT32 upper)
{
    return _imin_(_imax_(lower, middle), upper);
}

static inline long _itimediff(IUINT32 later, IUINT32 earlier)
{
    return ((IINT32)(later - earlier));
}

//---------------------------------------------------------------------
// manage segment
//---------------------------------------------------------------------
typedef struct IKCPSEG IKCPSEG;

static void *(*ikcp_malloc_hook)(size_t) = NULL;
static void (*ikcp_free_hook)(void *) = NULL;

// internal malloc
static void *ikcp_malloc(size_t size)
{
    if (ikcp_malloc_hook)
        return ikcp_malloc_hook(size);
    return malloc(size);
}

// internal free
static void ikcp_free(void *ptr)
{
    if (ikcp_free_hook)
    {
        ikcp_free_hook(ptr);
    }
    else
    {
        free(ptr);
    }
}

// redefine allocator
void ikcp_allocator(void *(*new_malloc)(size_t), void (*new_free)(void *))
{
    ikcp_malloc_hook = new_malloc;
    ikcp_free_hook = new_free;
}

// allocate a new kcp segment
static IKCPSEG *ikcp_segment_new(ikcpcb *kcp, int size)
{
    return (IKCPSEG *)ikcp_malloc(sizeof(IKCPSEG) + size);
}

// delete a segment
static void ikcp_segment_delete(ikcpcb *kcp, IKCPSEG *seg)
{
    ikcp_free(seg);
}

// write log
void ikcp_log(ikcpcb *kcp, int mask, const char *fmt, ...)
{
    char buffer[1024];
    va_list argptr;
    if ((mask & kcp->logmask) == 0 || kcp->writelog == 0) return;
    va_start(argptr, fmt);
    vsprintf(buffer, fmt, argptr);
    va_end(argptr);
    kcp->writelog(buffer, kcp, kcp->user);
}

// check log mask
static int ikcp_canlog(const ikcpcb *kcp, int mask)
{
    if ((mask & kcp->logmask) == 0 || kcp->writelog == NULL) return 0;
    return 1;
}

// output segment
static int ikcp_output(ikcpcb *kcp, const void *data, int size)
{
    assert(kcp);
    assert(kcp->output);
    if (ikcp_canlog(kcp, IKCP_LOG_OUTPUT))
    {
        ikcp_log(kcp, IKCP_LOG_OUTPUT, "[RO] %ld bytes", (long)size);
    }
    if (size == 0) return 0;
    return kcp->output((const char *)data, size, kcp, kcp->user);
}

// output queue
void ikcp_qprint(const char *name, const struct IQUEUEHEAD *head)
{
#if 0
    const struct IQUEUEHEAD *p;
    printf("<%s>: [", name);
    for (p = head->next; p != head; p = p->next)
    {
        const IKCPSEG *seg = iqueue_entry(p, const IKCPSEG, node);
        printf("(%lu %d)", (unsigned long)seg->sn, (int)(seg->ts % 10000));
        if (p->next != head) printf(",");
    }
    printf("]\n");
#endif
}


//---------------------------------------------------------------------
// create a new kcpcb
//---------------------------------------------------------------------
ikcpcb *ikcp_create(IUINT32 conv, void *user)
{
    ikcpcb *kcp = (ikcpcb *)ikcp_malloc(sizeof(struct IKCPCB));
    if (kcp == NULL) return NULL;
    kcp->conv = conv;
    kcp->user = user;
    kcp->snd_una = 0;
    kcp->snd_nxt = 0;
    kcp->rcv_nxt = 0;
    kcp->ts_recent = 0;
    kcp->ts_lastack = 0;
    kcp->ts_probe = 0;
    kcp->probe_wait = 0;
    kcp->snd_wnd = IKCP_WND_SND;
    kcp->rcv_wnd = IKCP_WND_RCV;
    kcp->rmt_wnd = IKCP_WND_RCV;
    kcp->cwnd = 0;
    kcp->incr = 0;
    kcp->probe = 0;
    kcp->mtu = IKCP_MTU_DEF;
    kcp->mss = kcp->mtu - IKCP_OVERHEAD;
    kcp->stream = 0;

    kcp->buffer = (char *)ikcp_malloc((kcp->mtu + IKCP_OVERHEAD) * 3);
    if (kcp->buffer == NULL)
    {
        ikcp_free(kcp);
        return NULL;
    }

    iqueue_init(&kcp->snd_queue);
    iqueue_init(&kcp->rcv_queue);
    iqueue_init(&kcp->snd_buf);
    iqueue_init(&kcp->rcv_buf);
    kcp->nrcv_buf = 0;
    kcp->nsnd_buf = 0;
    kcp->nrcv_que = 0;
    kcp->nsnd_que = 0;
    kcp->state = 0;
    kcp->acklist = NULL;
    kcp->ackblock = 0;
    kcp->ackcount = 0;
    kcp->rx_srtt = 0;
    kcp->rx_rttval = 0;
    kcp->rx_rto = IKCP_RTO_DEF;
    kcp->rx_minrto = IKCP_RTO_MIN;
    kcp->current = 0;
    kcp->interval = IKCP_INTERVAL;
    kcp->ts_flush = IKCP_INTERVAL;
    kcp->nodelay = 0;
    kcp->updated = 0;
    kcp->logmask = 0;
    kcp->ssthresh = IKCP_THRESH_INIT;
    kcp->fastresend = 0;
    kcp->nocwnd = 0;
    kcp->xmit = 0;
    kcp->dead_link = IKCP_DEADLINK;
    kcp->output = NULL;
    kcp->writelog = NULL;

    return kcp;
}


//---------------------------------------------------------------------
// release a new kcpcb
//---------------------------------------------------------------------
void ikcp_release(ikcpcb *kcp)
{
    assert(kcp);
    if (kcp)
    {
        IKCPSEG *seg;
        while (!iqueue_is_empty(&kcp->snd_buf))
        {
            seg = iqueue_entry(kcp->snd_buf.next, IKCPSEG, node);
            iqueue_del(&seg->node);
            ikcp_segment_delete(kcp, seg);
        }
        while (!iqueue_is_empty(&kcp->rcv_buf))
        {
            seg = iqueue_entry(kcp->rcv_buf.next, IKCPSEG, node);
            iqueue_del(&seg->node);
            ikcp_segment_delete(kcp, seg);
        }
        while (!iqueue_is_empty(&kcp->snd_queue))
        {
            seg = iqueue_entry(kcp->snd_queue.next, IKCPSEG, node);
            iqueue_del(&seg->node);
            ikcp_segment_delete(kcp, seg);
        }
        while (!iqueue_is_empty(&kcp->rcv_queue))
        {
            seg = iqueue_entry(kcp->rcv_queue.next, IKCPSEG, node);
            iqueue_del(&seg->node);
            ikcp_segment_delete(kcp, seg);
        }
        if (kcp->buffer)
        {
            ikcp_free(kcp->buffer);
        }
        if (kcp->acklist)
        {
            ikcp_free(kcp->acklist);
        }

        kcp->nrcv_buf = 0;
        kcp->nsnd_buf = 0;
        kcp->nrcv_que = 0;
        kcp->nsnd_que = 0;
        kcp->ackcount = 0;
        kcp->buffer = NULL;
        kcp->acklist = NULL;
        ikcp_free(kcp);
    }
}


//---------------------------------------------------------------------
// set output callback, which will be invoked by kcp
//---------------------------------------------------------------------
void ikcp_setoutput(ikcpcb *kcp, int (*output)(const char *buf, int len,
                    ikcpcb *kcp, void *user))
{
    kcp->output = output;
}


//---------------------------------------------------------------------
// user/upper level recv: returns size, returns below zero for EAGAIN
//---------------------------------------------------------------------
// 类似与socket中的recv函数，从rcv_queue中读取数据
int ikcp_recv(ikcpcb *kcp, char *buffer, int len)
{
    struct IQUEUEHEAD *p;
    int ispeek = (len < 0)? 1 : 0;
    int peeksize;
    int recover = 0;
    IKCPSEG *seg;
    assert(kcp);

    if (iqueue_is_empty(&kcp->rcv_queue))
        return -1;

    if (len < 0) len = -len;

    peeksize = ikcp_peeksize(kcp);

    if (peeksize < 0)
        return -2;

    if (peeksize > len)
        return -3;

    if (kcp->nrcv_que >= kcp->rcv_wnd) {  // 当前已经收的包大于接收窗口了，已经无法在收包了
        recover = 1;                    // 进入快速恢复状态，设置接收窗口是0，通知对端暂时不要在发送数据了
    }

    // merge fragment
    for (len = 0, p = kcp->rcv_queue.next; p != &kcp->rcv_queue; )
    {
        int fragment;
        seg = iqueue_entry(p, IKCPSEG, node);
        p = p->next;

        if (buffer)
        {
            memcpy(buffer, seg->data, seg->len);
            buffer += seg->len;
        }

        len += seg->len;
        fragment = seg->frg;

        if (ikcp_canlog(kcp, IKCP_LOG_RECV))
        {
            ikcp_log(kcp, IKCP_LOG_RECV, "recv sn=%lu", seg->sn);
        }

        if (ispeek == 0)  // peek一下，则rcv_queue中的数据就全部都删除掉了，会造成数据不连续呀？为什么是这么考虑的呢？
        {
            iqueue_del(&seg->node);
            ikcp_segment_delete(kcp, seg);
            kcp->nrcv_que--;
        }

        if (fragment == 0)
            break;
    }

    assert(len == peeksize);

    // move available data from rcv_buf -> rcv_queue
    while (! iqueue_is_empty(&kcp->rcv_buf))
    {
        IKCPSEG *seg = iqueue_entry(kcp->rcv_buf.next, IKCPSEG, node);
        if (seg->sn == kcp->rcv_nxt && kcp->nrcv_que < kcp->rcv_wnd)
        {
            // rcv_queue中已经有空闲位置了，将rcv_buf中已经连续的数据移动过去
            // 注意：seg->sn == kcp->rcv_nxt保证了数据的连续性
            iqueue_del(&seg->node);
            kcp->nrcv_buf--;
            iqueue_add_tail(&seg->node, &kcp->rcv_queue);
            kcp->nrcv_que++;
            kcp->rcv_nxt++;
        }
        else
        {
            break;
        }
    }

    // fast recover
    if (kcp->nrcv_que < kcp->rcv_wnd && recover)
    {
        // ready to send back IKCP_CMD_WINS in ikcp_flush
        // tell remote my window size
        kcp->probe |= IKCP_ASK_TELL;
    }

    return len;
}


//---------------------------------------------------------------------
// peek data size
//---------------------------------------------------------------------
int ikcp_peeksize(const ikcpcb *kcp)
{
    struct IQUEUEHEAD *p;
    IKCPSEG *seg;
    int length = 0;

    assert(kcp);

    if (iqueue_is_empty(&kcp->rcv_queue)) return -1;

    // 在包模式下，超过mss的数据会被切片，frg表示片ID，相关代码在 seg->frg = (kcp->stream == 0)? (count - i - 1) : 0;
    // 需要注意的是：
    // 1. frg不是单调递增的,sn才是单调底层的，
    // 2. 在上层每次调用send后，frg是单调递减的，则最后一个分片的frg是0，则可以实现包模式的读取数据
    // 在流模式下，超过mss的数据会被切片，但是frg恒为0，所以，在读取的时候，必然返回第一个分片的数据，也就是小于mss的数据，而不会返回rcv_queue中的所有数据
    // 详见：https://github.com/skywind3000/kcp/issues/76#issuecomment-299119667
    // 作者给的答复是kcp的流模式和tcp流模式语义不同
    seg = iqueue_entry(kcp->rcv_queue.next, IKCPSEG, node);
    if (seg->frg == 0) return seg->len;

    if (kcp->nrcv_que < seg->frg + 1) return -1;

    for (p = kcp->rcv_queue.next; p != &kcp->rcv_queue; p = p->next)
    {
        seg = iqueue_entry(p, IKCPSEG, node);
        length += seg->len;
        if (seg->frg == 0) break;  // 包模式的最后一个分片
    }

    return length;
}


//---------------------------------------------------------------------
// user/upper level send, returns below zero for error
//---------------------------------------------------------------------
int ikcp_send(ikcpcb *kcp, const char *buffer, int len)
{
    IKCPSEG *seg;
    int count, i;

    assert(kcp->mss > 0);
    if (len < 0) return -1;

    // append to previous segment in streaming mode (if possible)
    if (kcp->stream != 0)
    {
        if (!iqueue_is_empty(&kcp->snd_queue))
        {
            IKCPSEG *old = iqueue_entry(kcp->snd_queue.prev, IKCPSEG, node);
            if (old->len < kcp->mss)
            {
                int capacity = kcp->mss - old->len;
                int extend = (len < capacity)? len : capacity;
                seg = ikcp_segment_new(kcp, old->len + extend);
                assert(seg);
                if (seg == NULL)
                {
                    return -2;
                }
                iqueue_add_tail(&seg->node, &kcp->snd_queue);
                memcpy(seg->data, old->data, old->len);
                if (buffer)
                {
                    memcpy(seg->data + old->len, buffer, extend);
                    buffer += extend;
                }
                seg->len = old->len + extend;
                seg->frg = 0;
                len -= extend;
                iqueue_del_init(&old->node);
                ikcp_segment_delete(kcp, old);
            }
        }
        if (len <= 0)
        {
            return 0;
        }
    }

    if (len <= (int)kcp->mss) count = 1;
    else count = (len + kcp->mss - 1) / kcp->mss;

    if (count > 255) return -2;

    if (count == 0) count = 1;

    // fragment
    for (i = 0; i < count; i++)
    {
        int size = len > (int)kcp->mss ? (int)kcp->mss : len;
        seg = ikcp_segment_new(kcp, size);
        assert(seg);
        if (seg == NULL)
        {
            return -2;
        }
        if (buffer && len > 0)
        {
            memcpy(seg->data, buffer, size);
        }
        seg->len = size;
        seg->frg = (kcp->stream == 0)? (count - i - 1) : 0;
        iqueue_init(&seg->node);
        iqueue_add_tail(&seg->node, &kcp->snd_queue);
        kcp->nsnd_que++;
        if (buffer)
        {
            buffer += size;
        }
        len -= size;
    }

    return 0;
}


//---------------------------------------------------------------------
// parse ack
//---------------------------------------------------------------------
static void ikcp_update_ack(ikcpcb *kcp, IINT32 rtt)
{
    IINT32 rto = 0;
    if (kcp->rx_srtt == 0)      //第一次收到ack
    {
        kcp->rx_srtt = rtt;
        kcp->rx_rttval = rtt / 2;
    }
    else
    {
        long delta = rtt - kcp->rx_srtt;
        if (delta < 0) delta = -delta;                          // 当前rtt与平滑rtt的绝对值

        kcp->rx_rttval = (3 * kcp->rx_rttval + delta) / 4;      // 修正浮动rtt的值，3/4的原始浮动rtt，1/4的当前的差值
        kcp->rx_srtt = (7 * kcp->rx_srtt + rtt) / 8;            // 7/8的原始平滑rtt，1/8的当前rtt
        if (kcp->rx_srtt < 1) kcp->rx_srtt = 1;
    }
    // rto = 平滑rtt + 4倍的浮动rtt
    rto = kcp->rx_srtt + _imax_(kcp->interval, 4 * kcp->rx_rttval);
    kcp->rx_rto = _ibound_(kcp->rx_minrto, rto, IKCP_RTO_MAX);
}

static void ikcp_shrink_buf(ikcpcb *kcp)
{
    // 更新待确认的包snd_uma
    struct IQUEUEHEAD *p = kcp->snd_buf.next;
    if (p != &kcp->snd_buf)
    {
        IKCPSEG *seg = iqueue_entry(p, IKCPSEG, node);
        kcp->snd_una = seg->sn;
    }
    else
    {
        kcp->snd_una = kcp->snd_nxt;
    }
}

static void ikcp_parse_ack(ikcpcb *kcp, IUINT32 sn)
{
    // 根据ack从发送队列snd_buf中删除对方已经收到的包
    struct IQUEUEHEAD *p, *next;

    if (_itimediff(sn, kcp->snd_una) < 0 || _itimediff(sn, kcp->snd_nxt) >= 0)
        return;

    for (p = kcp->snd_buf.next; p != &kcp->snd_buf; p = next)
    {
        IKCPSEG *seg = iqueue_entry(p, IKCPSEG, node);
        next = p->next;
        if (sn == seg->sn)
        {
            // 通过ack将对方收到的sn删除掉，则在快速重传的场景中即可实现选择性重传(就是只重传对方没有收到的包)
            // 特性：选择性重传 vs 全部重传
            // 关联代码 ikcp_flush中的needsend
            iqueue_del(p);
            ikcp_segment_delete(kcp, seg);
            kcp->nsnd_buf--;
            break;
        }
        if (_itimediff(sn, seg->sn) < 0)
        {
            break;
        }
    }
}

static void ikcp_parse_una(ikcpcb *kcp, IUINT32 una)
{
    // 根据una从发送队列snd_buf中删除对方已经收到的包
    struct IQUEUEHEAD *p, *next;
    for (p = kcp->snd_buf.next; p != &kcp->snd_buf; p = next)
    {
        IKCPSEG *seg = iqueue_entry(p, IKCPSEG, node);
        next = p->next;
        if (_itimediff(una, seg->sn) > 0)
        {
            iqueue_del(p);
            ikcp_segment_delete(kcp, seg);
            kcp->nsnd_buf--;
        }
        else
        {
            break;
        }
    }
}

static void ikcp_parse_fastack(ikcpcb *kcp, IUINT32 sn)
{
    struct IQUEUEHEAD *p, *next;

    if (_itimediff(sn, kcp->snd_una) < 0 || _itimediff(sn, kcp->snd_nxt) >= 0)
        return;

    for (p = kcp->snd_buf.next; p != &kcp->snd_buf; p = next)
    {
        IKCPSEG *seg = iqueue_entry(p, IKCPSEG, node);
        next = p->next;
        if (_itimediff(sn, seg->sn) < 0)
        {
            break;
        }
        else if (sn != seg->sn)
        {
            seg->fastack++;     //接收端收到的包的序号大于发送端待确认包的序号
        }
    }
}


//---------------------------------------------------------------------
// ack append
//---------------------------------------------------------------------
static void ikcp_ack_push(ikcpcb *kcp, IUINT32 sn, IUINT32 ts)
{
    size_t newsize = kcp->ackcount + 1;
    IUINT32 *ptr;

    if (newsize > kcp->ackblock)
    {
        IUINT32 *acklist;
        size_t newblock;

        // 每次扩容为原来的一倍
        // 依次为8，16，32，64等
        for (newblock = 8; newblock < newsize; newblock <<= 1);
        acklist = (IUINT32 *)ikcp_malloc(newblock * sizeof(IUINT32) * 2);

        if (acklist == NULL)
        {
            assert(acklist != NULL);
            abort();
        }

        if (kcp->acklist != NULL)
        {
            size_t x;
            for (x = 0; x < kcp->ackcount; x++)
            {
                acklist[x * 2 + 0] = kcp->acklist[x * 2 + 0];
                acklist[x * 2 + 1] = kcp->acklist[x * 2 + 1];
            }
            ikcp_free(kcp->acklist);
        }

        kcp->acklist = acklist;
        kcp->ackblock = newblock;
    }

    ptr = &kcp->acklist[kcp->ackcount * 2];
    ptr[0] = sn;    // 存储包的序号和发包时间
    ptr[1] = ts;    // 将发包时间回射回去，发送端用来计算rtt
    kcp->ackcount++;
}

static void ikcp_ack_get(const ikcpcb *kcp, int p, IUINT32 *sn, IUINT32 *ts)
{
    if (sn) sn[0] = kcp->acklist[p * 2 + 0];
    if (ts) ts[0] = kcp->acklist[p * 2 + 1];
}


//---------------------------------------------------------------------
// parse data
//---------------------------------------------------------------------
void ikcp_parse_data(ikcpcb *kcp, IKCPSEG *newseg)
{
    struct IQUEUEHEAD *p, *prev;
    IUINT32 sn = newseg->sn;
    int repeat = 0;

    if (_itimediff(sn, kcp->rcv_nxt + kcp->rcv_wnd) >= 0 ||
            _itimediff(sn, kcp->rcv_nxt) < 0)
    {
        ikcp_segment_delete(kcp, newseg);
        return;
    }

    // 根据sn查找待插入的位置

    for (p = kcp->rcv_buf.prev; p != &kcp->rcv_buf; p = prev)
    {
        IKCPSEG *seg = iqueue_entry(p, IKCPSEG, node);
        prev = p->prev;
        if (seg->sn == sn)
        {
            repeat = 1;     //重复收到数据包
            break;
        }
        // 根据包ID来查找
        if (_itimediff(sn, seg->sn) > 0)
        {
            break;
        }
    }

    if (repeat == 0)
    {
        // 根据包ID来排序
        iqueue_init(&newseg->node);
        iqueue_add(&newseg->node, p);
        kcp->nrcv_buf++;
    }
    else
    {
        ikcp_segment_delete(kcp, newseg);
    }

#if 0
    ikcp_qprint("rcvbuf", &kcp->rcv_buf);
    printf("rcv_nxt=%lu\n", kcp->rcv_nxt);
#endif

    // move available data from rcv_buf -> rcv_queue
    while (! iqueue_is_empty(&kcp->rcv_buf))
    {
        IKCPSEG *seg = iqueue_entry(kcp->rcv_buf.next, IKCPSEG, node);
        if (seg->sn == kcp->rcv_nxt && kcp->nrcv_que < kcp->rcv_wnd)
        {
            // seg->sn == kcp->rcv_next 下一个待抛送的包已经到了
            iqueue_del(&seg->node);
            kcp->nrcv_buf--;
            iqueue_add_tail(&seg->node, &kcp->rcv_queue);
            kcp->nrcv_que++;
            kcp->rcv_nxt++;
        }
        else
        {
            break;
        }
    }

#if 0
    ikcp_qprint("queue", &kcp->rcv_queue);
    printf("rcv_nxt=%lu\n", kcp->rcv_nxt);
#endif

#if 1
//  printf("snd(buf=%d, queue=%d)\n", kcp->nsnd_buf, kcp->nsnd_que);
//  printf("rcv(buf=%d, queue=%d)\n", kcp->nrcv_buf, kcp->nrcv_que);
#endif
}


//---------------------------------------------------------------------
// input data
//---------------------------------------------------------------------
int ikcp_input(ikcpcb *kcp, const char *data, long size)
{
    IUINT32 una = kcp->snd_una;
    IUINT32 maxack = 0;
    int flag = 0;

    if (ikcp_canlog(kcp, IKCP_LOG_INPUT))
    {
        ikcp_log(kcp, IKCP_LOG_INPUT, "[RI] %d bytes", size);
    }

    if (data == NULL || size < IKCP_OVERHEAD) return -1;

    while (1)
    {
        IUINT32 ts, sn, len, una, conv;
        IUINT16 wnd;
        IUINT8 cmd, frg;
        IKCPSEG *seg;

        if (size < (int)IKCP_OVERHEAD) break;

        data = ikcp_decode32u(data, &conv);
        if (conv != kcp->conv) return -1;

        data = ikcp_decode8u(data, &cmd);
        data = ikcp_decode8u(data, &frg);
        data = ikcp_decode16u(data, &wnd);
        data = ikcp_decode32u(data, &ts);
        data = ikcp_decode32u(data, &sn);
        data = ikcp_decode32u(data, &una);
        data = ikcp_decode32u(data, &len);

        size -= IKCP_OVERHEAD;

        if ((long)size < (long)len) return -2;

        if (cmd != IKCP_CMD_PUSH && cmd != IKCP_CMD_ACK &&
                cmd != IKCP_CMD_WASK && cmd != IKCP_CMD_WINS)
            return -3;

        kcp->rmt_wnd = wnd;
        ikcp_parse_una(kcp, una);       //删除对端已经收到的包
        ikcp_shrink_buf(kcp);           //重置待确认包的序号snd_una

        if (cmd == IKCP_CMD_ACK)    // 收到ack包
        {
            if (_itimediff(kcp->current, ts) >= 0)
            {
                ikcp_update_ack(kcp, _itimediff(kcp->current, ts));     //通过rtt来计算rto
            }
            ikcp_parse_ack(kcp, sn);    //删除当前sn的包
            ikcp_shrink_buf(kcp);       //重置待确认包的序号snd_una
            if (flag == 0)
            {
                flag = 1;
                maxack = sn;
            }
            else
            {
                if (_itimediff(sn, maxack) > 0)
                {
                    maxack = sn;
                }
            }
            if (ikcp_canlog(kcp, IKCP_LOG_IN_ACK))
            {
                ikcp_log(kcp, IKCP_LOG_IN_DATA,
                         "input ack: sn=%lu rtt=%ld rto=%ld", sn,
                         (long)_itimediff(kcp->current, ts),
                         (long)kcp->rx_rto);
            }
        }
        else if (cmd == IKCP_CMD_PUSH)      //收到数据包
        {
            if (ikcp_canlog(kcp, IKCP_LOG_IN_DATA))
            {
                ikcp_log(kcp, IKCP_LOG_IN_DATA,
                         "input psh: sn=%lu ts=%lu", sn, ts);
            }
            if (_itimediff(sn, kcp->rcv_nxt + kcp->rcv_wnd) < 0)
            {
                ikcp_ack_push(kcp, sn, ts);                     //存储要发送的ack
                if (_itimediff(sn, kcp->rcv_nxt) >= 0)
                {
                    seg = ikcp_segment_new(kcp, len);
                    seg->conv = conv;
                    seg->cmd = cmd;
                    seg->frg = frg;
                    seg->wnd = wnd;
                    seg->ts = ts;
                    seg->sn = sn;
                    seg->una = una;
                    seg->len = len;

                    if (len > 0)
                    {
                        memcpy(seg->data, data, len);
                    }

                    ikcp_parse_data(kcp, seg);
                }
            }
        }
        else if (cmd == IKCP_CMD_WASK)      //探测窗口大小
        {
            // ready to send back IKCP_CMD_WINS in ikcp_flush
            // tell remote my window size
            kcp->probe |= IKCP_ASK_TELL;
            if (ikcp_canlog(kcp, IKCP_LOG_IN_PROBE))
            {
                ikcp_log(kcp, IKCP_LOG_IN_PROBE, "input probe");
            }
        }
        else if (cmd == IKCP_CMD_WINS)
        {
            // do nothing
            if (ikcp_canlog(kcp, IKCP_LOG_IN_WINS))
            {
                ikcp_log(kcp, IKCP_LOG_IN_WINS,
                         "input wins: %lu", (IUINT32)(wnd));
            }
        }
        else
        {
            return -3;
        }

        data += len;
        size -= len;
    }

    if (flag != 0)
    {
        ikcp_parse_fastack(kcp, maxack);
    }

    if (_itimediff(kcp->snd_una, una) > 0)
    {
        if (kcp->cwnd < kcp->rmt_wnd)
        {
            IUINT32 mss = kcp->mss;
            if (kcp->cwnd < kcp->ssthresh)
            {
                kcp->cwnd++;            //未达到慢启动阈值前，指数增长
                kcp->incr += mss;
            }
            else                        //达到慢启动阈值，
            {
                if (kcp->incr < mss) kcp->incr = mss;
                kcp->incr += (mss * mss) / kcp->incr + (mss / 16);   // mss/16=86
                if ((kcp->cwnd + 1) * mss <= kcp->incr)
                {
                    kcp->cwnd++;
                }
            }

            if (kcp->cwnd > kcp->rmt_wnd)
            {
                kcp->cwnd = kcp->rmt_wnd;
                kcp->incr = kcp->rmt_wnd * mss;
            }
        }
    }

    return 0;
}


//---------------------------------------------------------------------
// ikcp_encode_seg
//---------------------------------------------------------------------
static char *ikcp_encode_seg(char *ptr, const IKCPSEG *seg)
{
    ptr = ikcp_encode32u(ptr, seg->conv);
    ptr = ikcp_encode8u(ptr, (IUINT8)seg->cmd);
    ptr = ikcp_encode8u(ptr, (IUINT8)seg->frg);
    ptr = ikcp_encode16u(ptr, (IUINT16)seg->wnd);
    ptr = ikcp_encode32u(ptr, seg->ts);
    ptr = ikcp_encode32u(ptr, seg->sn);
    ptr = ikcp_encode32u(ptr, seg->una);
    ptr = ikcp_encode32u(ptr, seg->len);
    return ptr;
}

static int ikcp_wnd_unused(const ikcpcb *kcp)
{
    if (kcp->nrcv_que < kcp->rcv_wnd)
    {
        return kcp->rcv_wnd - kcp->nrcv_que;
    }
    return 0;
}


//---------------------------------------------------------------------
// ikcp_flush
//---------------------------------------------------------------------
void ikcp_flush(ikcpcb *kcp)
{
    IUINT32 current = kcp->current;
    char *buffer = kcp->buffer;
    char *ptr = buffer;
    int count, size, i;
    IUINT32 resent, cwnd;
    IUINT32 rtomin;
    struct IQUEUEHEAD *p;
    int change = 0;
    int lost = 0;
    IKCPSEG seg;

    // 'ikcp_update' haven't been called.
    if (kcp->updated == 0) return;

    seg.conv = kcp->conv;
    seg.cmd = IKCP_CMD_ACK;
    seg.frg = 0;
    seg.wnd = ikcp_wnd_unused(kcp);
    seg.una = kcp->rcv_nxt;
    seg.len = 0;
    seg.sn = 0;
    seg.ts = 0;

    // flush acknowledges
    count = kcp->ackcount;
    for (i = 0; i < count; i++)     // 发送ack
    {
        // 延迟ACK vs 非延迟ACK。延迟发送ack会导致计算出来的rtt偏大
        // 在flush中发送ack，就是延迟发送ack，因为flush是按照一定时间间隔调用的

        size = (int)(ptr - buffer);
        if (size + (int)IKCP_OVERHEAD > (int)kcp->mtu)
        {
            ikcp_output(kcp, buffer, size);
            ptr = buffer;
        }
        ikcp_ack_get(kcp, i, &seg.sn, &seg.ts);
        ptr = ikcp_encode_seg(ptr, &seg);
    }

    kcp->ackcount = 0;

    // probe window size (if remote window size equals zero)
    if (kcp->rmt_wnd == 0)      //接收端窗口为0时发送探测窗口的包
    {
        if (kcp->probe_wait == 0)
        {
            kcp->probe_wait = IKCP_PROBE_INIT;
            kcp->ts_probe = kcp->current + kcp->probe_wait;
        }
        else
        {
            if (_itimediff(kcp->current, kcp->ts_probe) >= 0)
            {
                if (kcp->probe_wait < IKCP_PROBE_INIT)
                    kcp->probe_wait = IKCP_PROBE_INIT;
                kcp->probe_wait += kcp->probe_wait / 2;     //窗口探测时间以1.5倍递增
                if (kcp->probe_wait > IKCP_PROBE_LIMIT)
                    kcp->probe_wait = IKCP_PROBE_LIMIT;
                kcp->ts_probe = kcp->current + kcp->probe_wait;
                kcp->probe |= IKCP_ASK_SEND;
            }
        }
    }
    else
    {
        kcp->ts_probe = 0;
        kcp->probe_wait = 0;
    }

    // flush window probing commands
    if (kcp->probe & IKCP_ASK_SEND)
    {
        seg.cmd = IKCP_CMD_WASK;        // 发送窗口探测包
        size = (int)(ptr - buffer);
        if (size + (int)IKCP_OVERHEAD > (int)kcp->mtu)
        {
            ikcp_output(kcp, buffer, size);
            ptr = buffer;
        }
        ptr = ikcp_encode_seg(ptr, &seg);
    }

    // flush window probing commands
    if (kcp->probe & IKCP_ASK_TELL)
    {
        seg.cmd = IKCP_CMD_WINS;        //回复窗口探测包
        size = (int)(ptr - buffer);
        if (size + (int)IKCP_OVERHEAD > (int)kcp->mtu)
        {
            ikcp_output(kcp, buffer, size);
            ptr = buffer;
        }
        ptr = ikcp_encode_seg(ptr, &seg);
    }

    kcp->probe = 0;

    // calculate window size
    cwnd = _imin_(kcp->snd_wnd, kcp->rmt_wnd);
    if (kcp->nocwnd == 0) cwnd = _imin_(kcp->cwnd, cwnd);   //wiki技术特性非退让流控

    // 在nocwnd为0，关闭流程的情况下，interval的最小值是10ms，在下一次调用flash之前，对端没有更新rmt_wnd窗口，则发送窗口仍然比较大

    // move data from snd_queue to snd_buf
    while (_itimediff(kcp->snd_nxt, kcp->snd_una + cwnd) < 0)
    {
        // 将发送队列的数据移动到当前轮可以发送的buffer中

        IKCPSEG *newseg;
        if (iqueue_is_empty(&kcp->snd_queue)) break;

        newseg = iqueue_entry(kcp->snd_queue.next, IKCPSEG, node);
        iqueue_del(&newseg->node);
        iqueue_add_tail(&newseg->node, &kcp->snd_buf);
        kcp->nsnd_que--;
        kcp->nsnd_buf++;

        newseg->conv = kcp->conv;
        newseg->cmd = IKCP_CMD_PUSH;
        newseg->wnd = seg.wnd;
        newseg->ts = current;
        newseg->sn = kcp->snd_nxt++;
        newseg->una = kcp->rcv_nxt;
        newseg->resendts = current;
        newseg->rto = kcp->rx_rto;
        newseg->fastack = 0;
        newseg->xmit = 0;
    }

    // calculate resent
    resent = (kcp->fastresend > 0)? (IUINT32)kcp->fastresend : 0xffffffff;  // 快速重传
    rtomin = (kcp->nodelay == 0)? (kcp->rx_rto >> 3) : 0;

    // flush data segments
    for (p = kcp->snd_buf.next; p != &kcp->snd_buf; p = p->next)
    {
        IKCPSEG *segment = iqueue_entry(p, IKCPSEG, node);
        int needsend = 0;
        if (segment->xmit == 0)   //第一次发送当前包
        {
            needsend = 1;
            segment->xmit++;
            segment->rto = kcp->rx_rto;
            segment->resendts = current + segment->rto + rtomin;
        }
        else if (_itimediff(current, segment->resendts) >= 0)   //超时(rto)为收到ack，超时重传
        {
            needsend = 1;
            segment->xmit++;
            kcp->xmit++;
            if (kcp->nodelay == 0)
            {
                segment->rto += kcp->rx_rto;                //wiki主页技术特性中rto翻倍
            }
            else
            {
                segment->rto += kcp->rx_rto / 2;            //wiki主页技术特性中rto*1.5
            }
            segment->resendts = current + segment->rto;
            lost = 1;                                       // 网络发生了丢包
        }
        else if (segment->fastack >= resent)    // 快速重传
        {
            needsend = 1;
            segment->xmit++;
            segment->fastack = 0;
            segment->resendts = current + segment->rto;
            change++;
        }

        if (needsend)
        {
            int size, need;
            segment->ts = current;
            segment->wnd = seg.wnd;
            segment->una = kcp->rcv_nxt;

            size = (int)(ptr - buffer);
            need = IKCP_OVERHEAD + segment->len;

            if (size + need > (int)kcp->mtu)
            {
                ikcp_output(kcp, buffer, size);
                ptr = buffer;
            }

            ptr = ikcp_encode_seg(ptr, segment);

            if (segment->len > 0)
            {
                memcpy(ptr, segment->data, segment->len);
                ptr += segment->len;
            }

            if (segment->xmit >= kcp->dead_link)
            {
                kcp->state = -1;
            }
        }
    }

    // flash remain segments
    size = (int)(ptr - buffer);
    if (size > 0)
    {
        ikcp_output(kcp, buffer, size);
    }

    // update ssthresh
    if (change)     // 发生了快速重传，则表示部分数据包丢了
    {
        IUINT32 inflight = kcp->snd_nxt - kcp->snd_una;
        kcp->ssthresh = inflight / 2;           //慢启动的阈值降为当前发送窗口的一半
        if (kcp->ssthresh < IKCP_THRESH_MIN)
            kcp->ssthresh = IKCP_THRESH_MIN;
        kcp->cwnd = kcp->ssthresh + resent;     //为什么要加resent，应该是rfc规定的吧
        kcp->incr = kcp->cwnd * kcp->mss;
    }

    if (lost)   // 网络发生了丢包，此时网络已经拥塞了
    {
        // 快速恢复
        kcp->ssthresh = cwnd / 2;       // 慢启动的阈值降为网络拥塞是窗口的一半
        if (kcp->ssthresh < IKCP_THRESH_MIN)
            kcp->ssthresh = IKCP_THRESH_MIN;
        kcp->cwnd = 1;                  // 拥塞窗口设置为1，慢启动过程
        kcp->incr = kcp->mss;
    }

    if (kcp->cwnd < 1)
    {
        kcp->cwnd = 1;
        kcp->incr = kcp->mss;
    }
}


//---------------------------------------------------------------------
// update state (call it repeatedly, every 10ms-100ms), or you can ask
// ikcp_check when to call it again (without ikcp_input/_send calling).
// 'current' - current timestamp in millisec.
//---------------------------------------------------------------------
void ikcp_update(ikcpcb *kcp, IUINT32 current)
{
    IINT32 slap;

    kcp->current = current;

    if (kcp->updated == 0)
    {
        kcp->updated = 1;
        kcp->ts_flush = kcp->current;
    }

    slap = _itimediff(kcp->current, kcp->ts_flush);

    if (slap >= 10000 || slap < -10000)
    {
        kcp->ts_flush = kcp->current;
        slap = 0;
    }

    if (slap >= 0)
    {
        kcp->ts_flush += kcp->interval;
        if (_itimediff(kcp->current, kcp->ts_flush) >= 0)
        {
            kcp->ts_flush = kcp->current + kcp->interval;
        }
        ikcp_flush(kcp);
    }
}


//---------------------------------------------------------------------
// Determine when should you invoke ikcp_update:
// returns when you should invoke ikcp_update in millisec, if there
// is no ikcp_input/_send calling. you can call ikcp_update in that
// time, instead of call update repeatly.
// Important to reduce unnacessary ikcp_update invoking. use it to
// schedule ikcp_update (eg. implementing an epoll-like mechanism,
// or optimize ikcp_update when handling massive kcp connections)
//---------------------------------------------------------------------
IUINT32 ikcp_check(const ikcpcb *kcp, IUINT32 current)
{
    IUINT32 ts_flush = kcp->ts_flush;
    IINT32 tm_flush = 0x7fffffff;
    IINT32 tm_packet = 0x7fffffff;
    IUINT32 minimal = 0;
    struct IQUEUEHEAD *p;

    if (kcp->updated == 0)
    {
        return current;
    }

    if (_itimediff(current, ts_flush) >= 10000 ||
            _itimediff(current, ts_flush) < -10000)
    {
        ts_flush = current;
    }

    if (_itimediff(current, ts_flush) >= 0)
    {
        return current;
    }

    tm_flush = _itimediff(ts_flush, current);

    for (p = kcp->snd_buf.next; p != &kcp->snd_buf; p = p->next)
    {
        const IKCPSEG *seg = iqueue_entry(p, const IKCPSEG, node);
        IINT32 diff = _itimediff(seg->resendts, current);
        if (diff <= 0)
        {
            return current;
        }
        if (diff < tm_packet) tm_packet = diff;
    }

    minimal = (IUINT32)(tm_packet < tm_flush ? tm_packet : tm_flush);
    if (minimal >= kcp->interval) minimal = kcp->interval;

    return current + minimal;
}



int ikcp_setmtu(ikcpcb *kcp, int mtu)
{
    char *buffer;
    if (mtu < 50 || mtu < (int)IKCP_OVERHEAD)
        return -1;
    buffer = (char *)ikcp_malloc((mtu + IKCP_OVERHEAD) * 3);
    if (buffer == NULL)
        return -2;
    kcp->mtu = mtu;
    kcp->mss = kcp->mtu - IKCP_OVERHEAD;
    ikcp_free(kcp->buffer);
    kcp->buffer = buffer;
    return 0;
}

int ikcp_interval(ikcpcb *kcp, int interval)
{
    if (interval > 5000) interval = 5000;
    else if (interval < 10) interval = 10;
    kcp->interval = interval;
    return 0;
}

int ikcp_nodelay(ikcpcb *kcp, int nodelay, int interval, int resend, int nc)
{
    if (nodelay >= 0)
    {
        kcp->nodelay = nodelay;
        if (nodelay)
        {
            kcp->rx_minrto = IKCP_RTO_NDL;
        }
        else
        {
            kcp->rx_minrto = IKCP_RTO_MIN;
        }
    }
    if (interval >= 0)
    {
        if (interval > 5000) interval = 5000;
        else if (interval < 10) interval = 10;
        kcp->interval = interval;
    }
    if (resend >= 0)
    {
        kcp->fastresend = resend;
    }
    if (nc >= 0)
    {
        kcp->nocwnd = nc;
    }
    return 0;
}


int ikcp_wndsize(ikcpcb *kcp, int sndwnd, int rcvwnd)
{
    if (kcp)
    {
        if (sndwnd > 0)
        {
            kcp->snd_wnd = sndwnd;
        }
        if (rcvwnd > 0)
        {
            kcp->rcv_wnd = rcvwnd;
        }
    }
    return 0;
}

int ikcp_waitsnd(const ikcpcb *kcp)
{
    return kcp->nsnd_buf + kcp->nsnd_que;
}


// read conv
IUINT32 ikcp_getconv(const void *ptr)
{
    IUINT32 conv;
    ikcp_decode32u((const char *)ptr, &conv);
    return conv;
}


