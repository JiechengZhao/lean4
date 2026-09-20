#include <lean/lean.h>
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <stdio.h>

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
