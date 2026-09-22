#include <lean/lean.h>
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/ioctl.h>
#include <sys/syscall.h>
#include <linux/perf_event.h>

LEAN_EXPORT lean_object* lean_bench_alloc_zeroed(lean_object* sz_obj) {
    size_t sz = lean_unbox(sz_obj);
    lean_object* arr = lean_alloc_sarray(1, sz, sz);
    memset(lean_to_sarray(arr)->m_data, 0, sz);
    return arr;
}

LEAN_EXPORT lean_object* lean_bench_raw_c(lean_object* b, lean_object* iters_obj) {
    size_t iters = lean_unbox(iters_obj);
    size_t sz = lean_sarray_size(b);
    uint8_t* data = lean_to_sarray(b)->m_data;
    for (size_t it = 0; it < iters; it++) {
        for (size_t i = 0; i < sz; i++) {
            data[i] = (uint8_t)(i & 0xFF);
        }
    }
    return b;
}

LEAN_EXPORT lean_object* lean_bench_eval_sink(lean_object* b) {
    __asm__ __volatile__("" : "+r"(b) : : "memory");
    return b;
}

LEAN_EXPORT uint64_t lean_bench_checksum(b_lean_obj_arg b) {
    size_t sz = lean_sarray_size(b);
    const uint8_t* data = lean_to_sarray(b)->m_data;
    uint64_t sum = 0;
    for (size_t i = 0; i < sz; i++) {
        sum = sum * 31 + data[i];
    }
    return sum;
}

/* --- Hardware PMU Performance Counters (perf_event_open) --- */

static int perf_fds[6] = {-1, -1, -1, -1, -1, -1};
static int perf_initialized = 0;

static int open_perf_counter(uint32_t type, uint64_t config) {
    struct perf_event_attr pe;
    memset(&pe, 0, sizeof(struct perf_event_attr));
    pe.type = type;
    pe.size = sizeof(struct perf_event_attr);
    pe.config = config;
    pe.disabled = 1;
    pe.exclude_kernel = 1;
    pe.exclude_hv = 1;
    return syscall(__NR_perf_event_open, &pe, 0, -1, -1, 0);
}

static void ensure_perf_init(void) {
    if (perf_initialized) return;
    perf_fds[0] = open_perf_counter(PERF_TYPE_HARDWARE, PERF_COUNT_HW_INSTRUCTIONS);
    perf_fds[1] = open_perf_counter(PERF_TYPE_HARDWARE, PERF_COUNT_HW_CPU_CYCLES);
    perf_fds[2] = open_perf_counter(PERF_TYPE_HARDWARE, PERF_COUNT_HW_BRANCH_INSTRUCTIONS);
    perf_fds[3] = open_perf_counter(PERF_TYPE_HARDWARE, PERF_COUNT_HW_BRANCH_MISSES);
    perf_fds[4] = open_perf_counter(PERF_TYPE_HARDWARE, PERF_COUNT_HW_CACHE_REFERENCES);
    perf_fds[5] = open_perf_counter(PERF_TYPE_HARDWARE, PERF_COUNT_HW_CACHE_MISSES);
    perf_initialized = 1;
}

LEAN_EXPORT lean_obj_res lean_bench_perf_start(lean_obj_arg _w) {
    ensure_perf_init();
    for (int i = 0; i < 6; i++) {
        if (perf_fds[i] >= 0) {
            ioctl(perf_fds[i], PERF_EVENT_IOC_RESET, 0);
            ioctl(perf_fds[i], PERF_EVENT_IOC_ENABLE, 0);
        }
    }
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_bench_perf_stop(lean_obj_arg _w) {
    uint64_t counts[6] = {0};
    for (int i = 0; i < 6; i++) {
        if (perf_fds[i] >= 0) {
            ioctl(perf_fds[i], PERF_EVENT_IOC_DISABLE, 0);
            uint64_t val = 0;
            if (read(perf_fds[i], &val, sizeof(val)) > 0) {
                counts[i] = val;
            }
        }
    }
    char buf[512];
    double ipc = counts[1] ? (double)counts[0] / counts[1] : 0.0;
    double br_miss_pct = counts[2] ? (100.0 * counts[3] / counts[2]) : 0.0;
    double ca_miss_pct = counts[4] ? (100.0 * counts[5] / counts[4]) : 0.0;
    snprintf(buf, sizeof(buf), "%lu|%lu|%.2f|%lu|%lu (%.2f%%)|%lu|%lu (%.2f%%)",
             counts[0], counts[1], ipc, counts[2], counts[3], br_miss_pct, counts[4], counts[5], ca_miss_pct);
    return lean_io_result_mk_ok(lean_mk_string(buf));
}
