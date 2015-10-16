#ifndef HEADER_OPCODES
#define HEADER_OPCODES

#include "common.h"

typedef struct {
  uint32_t r_m   : 4;
  uint32_t magic : 4;
  uint32_t r_s   : 4;
  uint32_t r_n   : 4;
  uint32_t r_d   : 4;
  uint32_t s     : 1;
  uint32_t a     : 1;
  uint32_t       : 6;
  uint32_t cond  : 4;
} op_mult_t;

typedef struct {
  uint32_t op2    : 12;
  uint32_t r_d    : 4;
  uint32_t r_n    : 4;
  uint32_t s      : 1;
  uint32_t opcode : 4;
  uint32_t i      : 1;
  uint32_t        : 2;
  uint32_t cond   : 4;
} op_data_proc_t;

typedef struct {
  uint32_t offset : 24;
  uint32_t l      : 1;
  uint32_t magic  : 3;
  uint32_t cond   : 4;
} op_branch_t;

typedef struct {
  uint32_t r_n    : 4;
  uint32_t magic  : 24;
  uint32_t cond   : 4;
} op_bx_t;

typedef struct {
  uint32_t offset : 12;
  uint32_t r_d    : 4;
  uint32_t r_n    : 4;
  uint32_t l      : 1;
  uint32_t w      : 1;
  uint32_t b      : 1;
  uint32_t u      : 1;
  uint32_t p      : 1;
  uint32_t i      : 1;
  uint32_t magic  : 2;
  uint32_t cond   : 4;
} op_sdt_t;

typedef struct {
  uint32_t reg_bits :  16;
  uint32_t r_n   :      4;
  uint32_t l     :      1;
  uint32_t w     :      1;
  uint32_t s     :      1;
  uint32_t u     :      1;
  uint32_t p     :      1;
  uint32_t magic :      3;
  uint32_t cond  :      4;
} op_bdt_t;

typedef struct {
  uint32_t      : 28;
  uint32_t cond : 4;
} op_generic_t;

#endif
