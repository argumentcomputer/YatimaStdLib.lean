#include <lean/lean.h>
#include <string.h>

#define intern inline static
#define l_arg b_lean_obj_arg
#define l_res lean_obj_res

intern l_res mk_byte_array_from(void* data, size_t len) {
    lean_sarray_object * o = (lean_sarray_object*)lean_alloc_object(
        sizeof(lean_sarray_object) + len
    );
    lean_set_st_header((lean_object*)o, LeanScalarArray, 1);
    o->m_size = len;
    o->m_capacity = len;
    memcpy(o->m_data, data, len);
    return (lean_object*)o;
}

extern l_res lean_uint16_to_byte_array(uint16_t n) {
    return mk_byte_array_from((void*)&n, 2);
}

extern l_res lean_uint32_to_byte_array(uint32_t n) {
    return mk_byte_array_from((void*)&n, 4);
}

extern l_res lean_uint64_to_byte_array(uint64_t n) {
    return mk_byte_array_from((void*)&n, 8);
}

extern l_res lean_byte_array_to_uint16(l_arg a) {
    return *((uint16_t*)lean_to_sarray(a)->m_data);
}

extern l_res lean_byte_array_to_uint32(l_arg a) {
    return *((uint32_t*)lean_to_sarray(a)->m_data);
}

extern l_res lean_byte_array_to_uint64(l_arg a) {
    return *((uint64_t*)lean_to_sarray(a)->m_data);
}

extern bool lean_byte_array_beq(l_arg a, l_arg b) {
    lean_sarray_object* oa = lean_to_sarray(a);
    lean_sarray_object* ob = lean_to_sarray(b);
    size_t sa = oa->m_size;
    if (sa == ob->m_size) return memcmp(oa->m_data, ob->m_data, sa) == 0;
    return false;
}

extern uint8_t lean_byte_array_ord(l_arg a, l_arg b) {
    lean_sarray_object* oa = lean_to_sarray(a);
    lean_sarray_object* ob = lean_to_sarray(b);
    size_t sa = oa->m_size;
    size_t sb = ob->m_size;
    if (sa == sb) {
        int diff = memcmp(oa->m_data, ob->m_data, sa);
        if (diff < 0) return 0;
        else if (diff == 0) return 1;
        return 2;
    }
    else if (sa < sb) return 0;
    return 2;
}
