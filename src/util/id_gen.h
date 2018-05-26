/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    id_gen.h

Abstract:

    Basic support for generating & recycling ids.

Author:

    Leonardo de Moura (leonardo) 2008-02-02.

Revision History:

--*/
#ifndef ID_GEN_H_
#define ID_GEN_H_

#include "util/vector.h"
#include "util/util.h"

class id_gen {
    unsigned        m_next_id;
    unsigned_vector m_free_ids;
public:
    id_gen(unsigned start = 0):m_next_id(start) {}
    
    unsigned mk() {
        unsigned r;
        if (m_free_ids.empty()) {
            r = m_next_id;
            m_next_id++;
        }
        else {
            r = m_free_ids.back();
            m_free_ids.pop_back();
        }
        return r;
    }
    
    void recycle(unsigned id) { 
        if (memory::is_out_of_memory())
            return;
        m_free_ids.push_back(id); 
    }
    
    void reset(unsigned start = 0) {
        m_next_id = start;
        m_free_ids.clear();
    }

    void cleanup(unsigned start = 0) {
        m_next_id = start;
        m_free_ids.finalize();
    }
    
    unsigned show_hash(){
      unsigned h = string_hash((char *)&m_free_ids[0],m_free_ids.size()*sizeof(unsigned),17);
      return hash_u_u(h,m_next_id);
    }

    /**
       \brief Return N if the range of ids generated by this module is in the set [0..N)
    */
    unsigned get_id_range() const { return m_next_id; }


    /**
       \brief Debugging support method: set m_next_id to the least value id' s.t. id' >= id and id' is not in m_free_ids.
       This method is only used to create small repros that exposes bugs in Z3.
    */
    unsigned set_next_id(unsigned id) {
        m_next_id = id;
        while (std::find(m_free_ids.begin(), m_free_ids.end(), m_next_id) != m_free_ids.end())
            m_next_id++;
        return m_next_id;
    }

    void display_free_ids(std::ostream & out) {
        ::display(out, m_free_ids.begin(), m_free_ids.end());
    }

};

#endif /* ID_GEN_H_ */
