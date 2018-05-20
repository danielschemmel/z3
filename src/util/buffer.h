/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    buffer.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2006-10-16.

Revision History:

--*/
#ifndef BUFFER_H_
#define BUFFER_H_

#include<string.h>
#include "util/memory_manager.h"

template<bool CHECK>
class checked_int64;
namespace subpaving { class power; }
namespace polynomial { class power; }
class mpz;
class parameter;
class symbol;
class rational;
class expr_offset;
class aig_lit;
class old_interval;
namespace nlsat { class interval; }
namespace sat { class literal; }
namespace smt {
    class literal;
    class model_value_dependency;
    template<typename Ext>
    struct theory_arith__linear_monomial; // refactored smt::theory_arith<Ext>::linear_monomial, so we can forward declare it
    template<typename Ext>
    struct theory_arith__row_entry; // refactored smt::theory_arith<Ext>::row_entry, so we can forward declare it
    template<typename Ext>
    struct theory_arith__col_entry; // refactored smt::theory_arith<Ext>::col_entry, so we can forward declare it
}
#include <utility>
#include <type_traits>
template<typename T, bool destro, unsigned size> struct buffer_specialized : std::false_type { };

template<> struct buffer_specialized<bool, false, 16> : std::true_type { };
template<> struct buffer_specialized<bool, true, 16> : std::true_type { };
template<> struct buffer_specialized<char, false, 16> : std::true_type { };
template<> struct buffer_specialized<char, true, 16> : std::true_type { };
template<> struct buffer_specialized<char, false, 1024> : std::true_type { };
template<> struct buffer_specialized<int, false, 16> : std::true_type { };
template<> struct buffer_specialized<int, false, 32> : std::true_type { };
template<> struct buffer_specialized<unsigned, true, 16> : std::true_type { };
template<> struct buffer_specialized<unsigned, false, 16> : std::true_type { };
template<> struct buffer_specialized<unsigned, false, 32> : std::true_type { };
template<> struct buffer_specialized<unsigned, false, 128> : std::true_type { };
template<> struct buffer_specialized<unsigned, false, 1024> : std::true_type { };
template<typename T> struct buffer_specialized<T*, false, 1> : std::true_type { };
template<typename T> struct buffer_specialized<T*, false, 8> : std::true_type { };
template<typename T> struct buffer_specialized<T*, false, 16> : std::true_type { };
template<typename T> struct buffer_specialized<T*, false, 32> : std::true_type { };
template<typename T> struct buffer_specialized<T*, false, 128> : std::true_type { };
template<typename T> struct buffer_specialized<T*, false, 256> : std::true_type { };
template<typename T> struct buffer_specialized<T*, false, 1024> : std::true_type { };
template<typename T> struct buffer_specialized<std::pair<checked_int64<true>, T*>, true, 2> : std::true_type { };
template<typename T> struct buffer_specialized<std::pair<rational, T*>, false, 16> : std::true_type { };
template<typename T> struct buffer_specialized<std::pair<T*, bool>, false, 64> : std::true_type { };
template<typename T> struct buffer_specialized<std::pair<T*, unsigned>, true, 16> : std::true_type { };
template<typename T> struct buffer_specialized<std::pair<T*, unsigned>, false, 16> : std::true_type { };
template<> struct buffer_specialized<mpz, false, 16> : std::true_type { };
template<> struct buffer_specialized<mpz, false, 128> : std::true_type { };
template<> struct buffer_specialized<subpaving::power, false, 16> : std::true_type { };
template<> struct buffer_specialized<polynomial::power, false, 16> : std::true_type { };
template<> struct buffer_specialized<polynomial::power, false, 32> : std::true_type { };
template<> struct buffer_specialized<parameter, true, 16> : std::true_type { };
template<> struct buffer_specialized<symbol, false, 16> : std::true_type { };
template<> struct buffer_specialized<symbol, true, 16> : std::true_type { };
template<> struct buffer_specialized<expr_offset, true, 16> : std::true_type { };
template<> struct buffer_specialized<rational, true, 16> : std::true_type { };
template<> struct buffer_specialized<aig_lit, false, 16> : std::true_type { };
template<> struct buffer_specialized<nlsat::interval, false, 128> : std::true_type { };
template<> struct buffer_specialized<sat::literal, false, 16> : std::true_type { };
template<> struct buffer_specialized<smt::literal, false, 16> : std::true_type { };
template<> struct buffer_specialized<smt::model_value_dependency, true, 16> : std::true_type { };
template<> struct buffer_specialized<old_interval, true, 16> : std::true_type { };
template<typename Ext> struct buffer_specialized<smt::theory_arith__linear_monomial<Ext>, true, 16> : std::true_type { };
template<typename Ext> struct buffer_specialized<smt::theory_arith__row_entry<Ext>, true, 16> : std::true_type { };
template<typename Ext> struct buffer_specialized<smt::theory_arith__col_entry<Ext>, true, 16> : std::true_type { };

template<typename T, bool CallDestructors=true, unsigned INITIAL_SIZE=16>
class buffer {
    static_assert(buffer_specialized<T, CallDestructors, INITIAL_SIZE>::value);

protected:
    T *      m_buffer;
    unsigned m_pos;
    unsigned m_capacity;
    char     m_initial_buffer[INITIAL_SIZE * sizeof(T)];
    
    void free_memory() {
        if (m_buffer != reinterpret_cast<T*>(m_initial_buffer)) {
            dealloc_svect(m_buffer);
        }
    }

    void expand() {
        unsigned new_capacity = m_capacity << 1;
        T * new_buffer        = reinterpret_cast<T*>(memory::allocate(sizeof(T) * new_capacity));
        memcpy(new_buffer, m_buffer, m_pos * sizeof(T));
        free_memory();
        m_buffer              = new_buffer;
        m_capacity            = new_capacity;
    }
    
    void destroy_elements() {
        iterator it = begin();
        iterator e  = end();
        for (; it != e; ++it) {
            it->~T();
        }
    }

    void destroy() {
        if (CallDestructors) {
            destroy_elements(); 
        }
        free_memory();
    }

public:
    typedef T data;
    typedef T * iterator;
    typedef const T * const_iterator;

    buffer():
        m_buffer(reinterpret_cast<T *>(m_initial_buffer)),
        m_pos(0),
        m_capacity(INITIAL_SIZE) {
    }
    
    buffer(const buffer & source):
        m_buffer(reinterpret_cast<T *>(m_initial_buffer)),
        m_pos(0),
        m_capacity(INITIAL_SIZE) {
        unsigned sz = source.size();
        for(unsigned i = 0; i < sz; i++) {
            push_back(source.m_buffer[i]);
        }
    }
    
    buffer(unsigned sz, const T & elem):
        m_buffer(reinterpret_cast<T *>(m_initial_buffer)),
        m_pos(0),
        m_capacity(INITIAL_SIZE) {
        for (unsigned i = 0; i < sz; i++) {
            push_back(elem);
        }
        SASSERT(size() == sz);
    }
    
    ~buffer() {
        destroy();
    }
    
    void reset() { 
        if (CallDestructors) {
            destroy_elements();
        }
        m_pos = 0;
    }
    
    void finalize() {
        destroy();
        m_buffer   = reinterpret_cast<T *>(m_initial_buffer);
        m_pos      = 0;
        m_capacity = INITIAL_SIZE;
    }
    
    unsigned size() const { 
        return m_pos;
    }
    
    bool empty() const {
        return m_pos == 0;
    }
    
    iterator begin() { 
        return m_buffer; 
    }

    iterator end() { 
        return m_buffer + size();
    }

    void set_end(iterator it) {
        m_pos = static_cast<unsigned>(it - m_buffer);
        if (CallDestructors) {
            iterator e  = end();
            for (; it != e; ++it) {
                it->~T();
            }
        }
    }
    
    const_iterator begin() const { 
        return m_buffer; 
    }
    
    const_iterator end() const { 
        return m_buffer + size(); 
    }
    
    void push_back(const T & elem) {
        if (m_pos >= m_capacity)
            expand();
        new (m_buffer + m_pos) T(elem);
        m_pos++;
    }

    void push_back(T && elem) {
        if (m_pos >= m_capacity)
            expand();
        new (m_buffer + m_pos) T(std::move(elem));
        m_pos++;
    }
    
    void pop_back() {
        if (CallDestructors) {
            back().~T(); 
        }
        m_pos--;
    }

    const T & back() const { 
        SASSERT(!empty()); 
        SASSERT(m_pos > 0);
        return m_buffer[m_pos - 1]; 
    }

    T & back() { 
        SASSERT(!empty()); 
        SASSERT(m_pos > 0);
        return m_buffer[m_pos - 1]; 
    }
    
    T * c_ptr() const {
        return m_buffer;
    }

    void append(unsigned n, T const * elems) {
        for (unsigned i = 0; i < n; i++) {
            push_back(elems[i]);
        }
    }

    void append(const buffer& source) {
        append(source.size(), source.c_ptr());
    }

    T & operator[](unsigned idx) { 
        SASSERT(idx < size()); 
        return m_buffer[idx]; 
    }

    const T & operator[](unsigned idx) const { 
        SASSERT(idx < size()); 
        return m_buffer[idx];
    }

    T & get(unsigned idx) { 
        SASSERT(idx < size()); 
        return m_buffer[idx]; 
    }

    const T & get(unsigned idx) const { 
        SASSERT(idx < size()); 
        return m_buffer[idx];
    }

    void set(unsigned idx, T const & val) { 
        SASSERT(idx < size()); 
        m_buffer[idx] = val;
    }

    void resize(unsigned nsz, const T & elem=T()) {
        unsigned sz = size();
        if (nsz > sz) {
            for (unsigned i = sz; i < nsz; i++) {
                push_back(elem);
            }
        }
        else if (nsz < sz) {
            for (unsigned i = nsz; i < sz; i++) {
                pop_back();
            }
        }
        SASSERT(size() == nsz);
    }

    void shrink(unsigned nsz) {
        unsigned sz = size();
        SASSERT(nsz <= sz);
        for (unsigned i = nsz; i < sz; i++)
            pop_back();
        SASSERT(size() == nsz);
    }

    buffer & operator=(buffer const & other) {
        if (this == &other)
            return *this;
        reset();
        append(other);
        return *this;
    }
};

template<typename T, unsigned INITIAL_SIZE=16>
class ptr_buffer : public buffer<T *, false, INITIAL_SIZE> {
public:
    void append(unsigned n, T * const * elems) {
        for (unsigned i = 0; i < n; i++) {
            this->push_back(elems[i]);
        }
    }
};

template<typename T, unsigned INITIAL_SIZE=16>
class sbuffer : public buffer<T, false, INITIAL_SIZE> {
public:
    sbuffer(): buffer<T, false, INITIAL_SIZE>() {}
    sbuffer(unsigned sz, const T& elem) : buffer<T, false, INITIAL_SIZE>(sz,elem) {}
};

#endif /* BUFFER_H_ */

