/* TI C6X assembler.
   Copyright (C) 2010-2025 Free Software Foundation, Inc.
   Contributed by Joseph Myers <joseph@codesourcery.com>
   		  Bernd Schmidt  <bernds@codesourcery.com>

   This file is part of GAS, the GNU Assembler.

   GAS is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3, or (at your option)
   any later version.

   GAS is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with GAS; see the file COPYING.  If not, write to the Free
   Software Foundation, 51 Franklin Street - Fifth Floor, Boston, MA
   02110-1301, USA.  */

#include "as.h"
#include "dwarf2dbg.h"
#include "dw2gencfi.h"
#include "safe-ctype.h"
#include "subsegs.h"
#include "opcode/tic6x.h"
#include "elf/tic6x.h"
#include "elf32-tic6x.h"

/* Truncate and sign-extend at 32 bits, so that building on a 64-bit
   host gives identical results to a 32-bit host.  */
#define TRUNC(X)	((valueT) (X) & 0xffffffffU)
#define SEXT(X)		((TRUNC (X) ^ 0x80000000U) - 0x80000000U)

#define streq(a, b)           (strcmp (a, b) == 0)

/* Stuff for .scomm symbols.  */
static segT sbss_section;
static asection scom_section;
static asymbol scom_symbol;

const char comment_chars[] = ";";
const char line_comment_chars[] = "#*;";
const char line_separator_chars[] = "@";

const char EXP_CHARS[] = "eE";
const char FLT_CHARS[] = "dDfF";

const char md_shortopts[] = "";

enum
  {
    OPTION_MARCH = OPTION_MD_BASE,
    OPTION_MBIG_ENDIAN,
    OPTION_MLITTLE_ENDIAN,
    OPTION_MDSBT,
    OPTION_MNO_DSBT,
    OPTION_MPID,
    OPTION_MPIC,
    OPTION_MNO_PIC,
    OPTION_MGENERATE_REL
  };

const struct option md_longopts[] =
  {
    { "march", required_argument, NULL, OPTION_MARCH },
    { "mbig-endian", no_argument, NULL, OPTION_MBIG_ENDIAN },
    { "mlittle-endian", no_argument, NULL, OPTION_MLITTLE_ENDIAN },
    { "mdsbt", no_argument, NULL, OPTION_MDSBT },
    { "mno-dsbt", no_argument, NULL, OPTION_MNO_DSBT },
    { "mpid", required_argument, NULL, OPTION_MPID },
    { "mpic", no_argument, NULL, OPTION_MPIC },
    { "mno-pic", no_argument, NULL, OPTION_MNO_PIC },
    { "mgenerate-rel", no_argument, NULL, OPTION_MGENERATE_REL },
    { NULL, no_argument, NULL, 0 }
  };
const size_t md_longopts_size = sizeof (md_longopts);

/* The instructions enabled based only on the selected architecture
   (all instructions, if no architecture specified).  */
static unsigned short tic6x_arch_enable = (TIC6X_INSN_C62X
					   | TIC6X_INSN_C64X
					   | TIC6X_INSN_C64XP
					   | TIC6X_INSN_C67X
					   | TIC6X_INSN_C67XP
					   | TIC6X_INSN_C674X);

/* The instructions enabled based on the current set of features
   (architecture, as modified by other options).  */
static unsigned short tic6x_features;

/* The architecture attribute value, or C6XABI_Tag_ISA_none if
   not yet set.  */
static int tic6x_arch_attribute = C6XABI_Tag_ISA_none;

/* Whether any instructions at all have been seen.  Once any
   instructions have been seen, architecture attributes merge into the
   previous attribute value rather than replacing it.  */
static bool tic6x_seen_insns = false;

/* The number of registers in each register file supported by the
   current architecture.  */
static unsigned int tic6x_num_registers;

/* Whether predication on A0 is possible.  */
static bool tic6x_predicate_a0;

/* Whether execute packets can cross fetch packet boundaries.  */
static bool tic6x_can_cross_fp_boundary;

/* Whether there are constraints on simultaneous reads and writes of
   40-bit data.  */
static bool tic6x_long_data_constraints;

/* Whether compact instructions are available.  */
static bool tic6x_compact_insns;

/* Whether to generate RELA relocations.  */
static bool tic6x_generate_rela = true;

/* Whether the code uses DSBT addressing.  */
static bool tic6x_dsbt;

/* Types of position-independent data (attribute values for
   Tag_ABI_PID).  */
typedef enum
  {
    tic6x_pid_no = 0,
    tic6x_pid_near = 1,
    tic6x_pid_far = 2
  } tic6x_pid_type;

/* The type of data addressing used in this code.  */
static tic6x_pid_type tic6x_pid;

/* Whether the code uses position-independent code.  */
static bool tic6x_pic;

/* Table of supported architecture variants.  */
typedef struct
{
  const char *arch;
  int attr;
  unsigned short features;
} tic6x_arch_table;
static const tic6x_arch_table tic6x_arches[] =
  {
    { "c62x", C6XABI_Tag_ISA_C62X, TIC6X_INSN_C62X },
    { "c64x", C6XABI_Tag_ISA_C64X, TIC6X_INSN_C62X | TIC6X_INSN_C64X },
    { "c64x+", C6XABI_Tag_ISA_C64XP, (TIC6X_INSN_C62X
				      | TIC6X_INSN_C64X
				      | TIC6X_INSN_C64XP) },
    { "c67x", C6XABI_Tag_ISA_C67X, TIC6X_INSN_C62X | TIC6X_INSN_C67X },
    { "c67x+", C6XABI_Tag_ISA_C67XP, (TIC6X_INSN_C62X
				      | TIC6X_INSN_C67X
				      | TIC6X_INSN_C67XP) },
    { "c674x", C6XABI_Tag_ISA_C674X, (TIC6X_INSN_C62X
				      | TIC6X_INSN_C64X
				      | TIC6X_INSN_C64XP
				      | TIC6X_INSN_C67X
				      | TIC6X_INSN_C67XP
				      | TIC6X_INSN_C674X) }
  };

/* Caller saved register encodings.  The standard frame layout uses this
   order, starting from the highest address.  There must be
   TIC6X_NUM_UNWIND_REGS values.  */
enum
{
  UNWIND_A15,
  UNWIND_B15,
  UNWIND_B14,
  UNWIND_B13,
  UNWIND_B12,
  UNWIND_B11,
  UNWIND_B10,
  UNWIND_B3,
  UNWIND_A14,
  UNWIND_A13,
  UNWIND_A12,
  UNWIND_A11,
  UNWIND_A10
};

static void tic6x_output_unwinding (bool need_extab);

/* Return the frame unwind state for the current function, allocating
   as necessary.  */

static tic6x_unwind_info *tic6x_get_unwind (void)
{
  tic6x_unwind_info *unwind_ptr = NULL;

  // First, attempt to retrieve unwind information from the primary 'unwind' field.
  unwind_ptr = seg_info(now_seg)->tc_segment_info_data.unwind;

  // If the primary field is empty, attempt to retrieve from the 'text_unwind' field.
  if (unwind_ptr == NULL) {
    unwind_ptr = seg_info(now_seg)->tc_segment_info_data.text_unwind;
  }

  // If both existing fields are empty, allocate a new tic6x_unwind_info structure.
  if (unwind_ptr == NULL) {
    // XNEW is assumed to be a robust allocation macro or function that handles
    // memory allocation failures internally (e.g., by terminating the program).
    // Therefore, no explicit NULL check is added immediately after XNEW,
    // preserving the original function's implied error handling strategy.
    unwind_ptr = XNEW(tic6x_unwind_info);

    // Store the newly allocated unwind information in the primary 'unwind' field
    // of the segment, consistent with the original function's logic.
    seg_info(now_seg)->tc_segment_info_data.unwind = unwind_ptr;
    
    // Initialize the entire newly allocated memory block to zeros for
    // security (avoiding uninitialized data exposure) and consistency.
    memset(unwind_ptr, 0, sizeof(*unwind_ptr));
  }

  return unwind_ptr;
}

/* Update the selected architecture based on ARCH, giving an error if
   ARCH is an invalid value.  Does not call tic6x_update_features; the
   caller must do that if necessary.  */

static void
tic6x_use_arch (const char *arch)
{
  if (arch == NULL)
    {
      as_bad (_("internal error: architecture name cannot be NULL"));
      return;
    }

  for (size_t i = 0; i < ARRAY_SIZE (tic6x_arches); i++)
    {
      if (strcmp (arch, tic6x_arches[i].arch) == 0)
        {
          tic6x_arch_enable = tic6x_arches[i].features;

          if (tic6x_seen_insns)
            {
              tic6x_arch_attribute = elf32_tic6x_merge_arch_attributes (
                                          tic6x_arch_attribute,
                                          tic6x_arches[i].attr);
            }
          else
            {
              tic6x_arch_attribute = tic6x_arches[i].attr;
            }
          return;
        }
    }

  as_bad (_("unknown architecture '%s'"), arch);
}

/* Table of supported -mpid arguments.  */
typedef struct
{
  const char *arg;
  tic6x_pid_type attr;
} tic6x_pid_type_table;
static const tic6x_pid_type_table tic6x_pid_types[] =
  {
    { "no", tic6x_pid_no },
    { "near", tic6x_pid_near },
    { "far", tic6x_pid_far }
  };

/* Handle -mpid=ARG.  */

static void
tic6x_use_pid (const char *arg)
{
  size_t i;

  for (i = 0; i < ARRAY_SIZE (tic6x_pid_types); i++)
    {
      if (strcmp (arg, tic6x_pid_types[i].arg) == 0)
        {
          tic6x_pid = tic6x_pid_types[i].attr;
          return;
        }
    }

  as_bad (_("unknown -mpid= argument '%s'"), arg);
}

/* Parse a target-specific option.  */

int
md_parse_option (int c, const char *arg)
{
  switch (c)
    {
    case OPTION_MARCH:
      if (!tic6x_use_arch (arg))
        {
          return 0;
        }
      break;

    case OPTION_MBIG_ENDIAN:
      target_big_endian = true;
      break;

    case OPTION_MLITTLE_ENDIAN:
      target_big_endian = false;
      break;

    case OPTION_MDSBT:
      tic6x_dsbt = true;
      break;

    case OPTION_MNO_DSBT:
      tic6x_dsbt = false;
      break;

    case OPTION_MPID:
      if (!tic6x_use_pid (arg))
        {
          return 0;
        }
      break;

    case OPTION_MPIC:
      tic6x_pic = true;
      break;

    case OPTION_MNO_PIC:
      tic6x_pic = false;
      break;

    case OPTION_MGENERATE_REL:
      tic6x_generate_rela = false;
      break;

    default:
      return 0;
    }
  return 1;
}

void
md_show_usage (FILE *stream)
{
  if (stream == NULL)
    {
      return;
    }

  unsigned int i;

  fputc ('\n', stream);
  fprintf (stream, _("TMS320C6000 options:\n"));
  fprintf (stream, _("  -march=ARCH             enable instructions from architecture ARCH\n"));
  fprintf (stream, _("  -mbig-endian            generate big-endian code\n"));
  fprintf (stream, _("  -mlittle-endian         generate little-endian code\n"));
  fprintf (stream, _("  -mdsbt                  code uses DSBT addressing\n"));
  fprintf (stream, _("  -mno-dsbt               code does not use DSBT addressing\n"));
  fprintf (stream, _("  -mpid=no                code uses position-dependent data addressing\n"));
  fprintf (stream, _("  -mpid=near              code uses position-independent data addressing,\n"
		     "                            GOT accesses use near DP addressing\n"));
  fprintf (stream, _("  -mpid=far               code uses position-independent data addressing,\n"
		     "                            GOT accesses use far DP addressing\n"));
  fprintf (stream, _("  -mpic                   code addressing is position-independent\n"));
  fprintf (stream, _("  -mno-pic                code addressing is position-dependent\n"));

  fputc ('\n', stream);
  fprintf (stream, _("Supported ARCH values are:"));
  for (i = 0; i < ARRAY_SIZE (tic6x_arches); i++)
    fprintf (stream, " %s", tic6x_arches[i].arch);
  fputc ('\n', stream);
}

/* Update enabled features based on the current architecture and
   related settings.  */
static void
tic6x_update_features (void)
{
  const unsigned int enable_mask = tic6x_arch_enable;

  const int has_c64x = (enable_mask & TIC6X_INSN_C64X) != 0;
  const int has_c67xp = (enable_mask & TIC6X_INSN_C67XP) != 0;
  const int has_c64xp = (enable_mask & TIC6X_INSN_C64XP) != 0;

  const int has_c64x_or_c67xp = has_c64x || has_c67xp;

  tic6x_features = enable_mask;

  tic6x_num_registers = has_c64x_or_c67xp ? 32 : 16;

  tic6x_predicate_a0 = has_c64x;

  tic6x_can_cross_fp_boundary = has_c64x_or_c67xp;

  tic6x_long_data_constraints = !has_c64x;

  tic6x_compact_insns = has_c64xp;
}

/* Do configuration after all options have been parsed.  */

void
tic6x_after_parse_args (void)
{
  tic6x_update_features ();
  return;
}

/* Parse a .cantunwind directive.  */
static void
s_tic6x_cantunwind (int ignored ATTRIBUTE_UNUSED)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();

  if (unwind->data_bytes == 0)
    {
      return;
    }

  if (unwind->data_bytes != -1)
    {
      as_bad (_("unexpected .cantunwind directive"));
      return;
    }

  demand_empty_rest_of_line ();

  if (unwind->personality_routine != NULL || unwind->personality_index != -1)
    {
      as_bad (_("personality routine specified for cantunwind frame"));
    }

  unwind->personality_index = -2;
}

/* Parse a .handlerdata directive.  */
static void
s_tic6x_handlerdata (int ignored ATTRIBUTE_UNUSED)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();

  if (!unwind->saved_seg)
    {
      as_bad (_("unexpected .handlerdata directive"));
      return;
    }

  if (unwind->table_entry || unwind->personality_index == -2)
    {
      as_bad (_("duplicate .handlerdata directive"));
      return;
    }

  if (unwind->personality_index == -1 && unwind->personality_routine == NULL)
    {
      as_bad (_("personality routine required before .handlerdata directive"));
      return;
    }

  tic6x_output_unwinding (true);
}

/* Parse a .endp directive.  */
static void
s_tic6x_endp (int ignored ATTRIBUTE_UNUSED)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();

  if (unwind == NULL)
    {
      return;
    }

  if (unwind->data_bytes != 0)
    {
      if (!unwind->table_entry)
	tic6x_output_unwinding (false);

      subseg_set (unwind->saved_seg, unwind->saved_subseg);
    }

  unwind->saved_seg = NULL;
  unwind->table_entry = NULL;
  unwind->data_bytes = 0;
}

/* Parse a .personalityindex directive.  */
static void
s_tic6x_personalityindex (int ignored ATTRIBUTE_UNUSED)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();
  expressionS exp;

  if (unwind->personality_routine != NULL || unwind->personality_index != -1)
    {
      as_bad (_("duplicate .personalityindex directive"));
      ignore_rest_of_line ();
      return;
    }

  expression (&exp);

  if (exp.X_op != O_constant
      || exp.X_add_number < 0 || exp.X_add_number > 15)
    {
      as_bad (_("bad personality routine number: must be an integer between 0 and 15"));
      ignore_rest_of_line ();
      return;
    }

  unwind->personality_index = exp.X_add_number;

  demand_empty_rest_of_line ();
}

static void
s_tic6x_personality (int ignored ATTRIBUTE_UNUSED)
{
  char *name;
  char c;
  tic6x_unwind_info *unwind = tic6x_get_unwind ();

  if (unwind == NULL)
    {
      as_bad (_("internal error: failed to retrieve unwind information"));
      return;
    }

  if (unwind->personality_routine || unwind->personality_index != -1)
    {
      as_bad (_("duplicate .personality directive"));
      return;
    }

  c = get_symbol_name (&name);
  unwind->personality_routine = symbol_find_or_make (name);
  (void) restore_line_pointer (c);
  demand_empty_rest_of_line ();
}

/* Parse a .arch directive.  */
static void
s_tic6x_arch (int ignored ATTRIBUTE_UNUSED)
{
  const char *start_of_arch_token = input_line_pointer;
  char *current_pos = input_line_pointer;

  while (!is_end_of_stmt (*current_pos) && !is_whitespace (*current_pos))
  {
    current_pos++;
  }

  size_t arch_len = current_pos - start_of_arch_token;

  char arch_buffer[arch_len + 1];
  strncpy(arch_buffer, start_of_arch_token, arch_len);
  arch_buffer[arch_len] = '\0';

  tic6x_use_arch (arch_buffer);
  tic6x_update_features ();

  input_line_pointer = current_pos;

  demand_empty_rest_of_line ();
}

/* Parse a .ehtype directive.  */

static void
s_tic6x_ehtype (void)
{
  expressionS exp;
  char *p;

#ifdef md_flush_pending_output
  md_flush_pending_output ();
#endif

  if (is_it_end_of_statement ())
    {
      demand_empty_rest_of_line ();
      return;
    }

#ifdef md_cons_align
  md_cons_align (4);
#endif

  expression (&exp);

  if (exp.X_op != O_symbol)
    {
      as_bad (_("expected symbol"));
      return;
    }

  p = frag_more (4);
  memset (p, 0, 4);
  fix_new_exp (frag_now, p - frag_now->fr_literal, 4,
	       &exp, 0, BFD_RELOC_C6000_EHTYPE);

  demand_empty_rest_of_line ();
}

/* Parse a .nocmp directive.  */

static void
s_tic6x_nocmp (int ignored ATTRIBUTE_UNUSED)
{
  struct seg_info_type *current_segment_info = seg_info(now_seg);

  if (current_segment_info == NULL) {
    return;
  }

  current_segment_info->tc_segment_info_data.nocmp = true;
  demand_empty_rest_of_line ();
}

/* .scomm pseudo-op handler.

   This is a new pseudo-op to handle putting objects in .scommon.
   By doing this the linker won't need to do any work,
   and more importantly it removes the implicit -G arg necessary to
   correctly link the object file.  */

static int
get_and_validate_alignment (offsetT *align_val, int *align2_val)
{
  offsetT align_expr;
  int align_log2;

  if (*input_line_pointer != ',')
    align_expr = 8; /* DEFAULT_SCOMM_ALIGNMENT */
  else
    {
      ++input_line_pointer;
      align_expr = get_absolute_expression ();
      if (align_expr <= 0)
	{
	  as_warn (_("alignment is not a positive number; using default %d"), 8 /* DEFAULT_SCOMM_ALIGNMENT */);
	  align_expr = 8; /* DEFAULT_SCOMM_ALIGNMENT */
	}
    }

  if (align_expr == 0)
    {
      align_log2 = 0;
    }
  else
    {
      offsetT temp_align = align_expr;
      align_log2 = 0;
      for (; (temp_align & 1) == 0 && temp_align != 0; temp_align >>= 1, ++align_log2)
        ;
      
      if (temp_align != 1)
	{
	  as_bad (_("alignment %ld is not a power of 2"), (long) align_expr);
	  return 0;
	}
    }

  *align_val = align_expr;
  *align2_val = align_log2;
  return 1;
}

static void
handle_local_scomm_symbol (symbolS *symbolP, offsetT size, int align_log2)
{
  segT old_sec = now_seg;
  int old_subsec = now_subseg;

  record_alignment (sbss_section, align_log2);
  subseg_set (sbss_section, 0);

  if (align_log2)
    frag_align (align_log2, 0, 0);

  if (S_GET_SEGMENT (symbolP) == sbss_section && symbol_get_frag (symbolP) != NULL)
    symbol_get_frag (symbolP)->fr_symbol = 0;

  symbol_set_frag (symbolP, frag_now);

  char *pfrag_start = frag_var (rs_org, 1, 1, 0, symbolP, size, NULL);
  if (pfrag_start != NULL)
    *pfrag_start = 0;

  S_SET_SIZE (symbolP, size);
  S_SET_SEGMENT (symbolP, sbss_section);
  S_CLEAR_EXTERNAL (symbolP);

  subseg_set (old_sec, old_subsec);
}

static void
s_tic6x_scomm (int ignore ATTRIBUTE_UNUSED)
{
  char *name;
  char delimiter_char;
  char *delimiter_ptr;
  offsetT size;
  symbolS *symbolP;
  offsetT align_val;
  int align_log2;

  delimiter_char = get_symbol_name (&name);
  
  delimiter_ptr = input_line_pointer;
  (void) restore_line_pointer (delimiter_char);
  SKIP_WHITESPACE ();
  if (*input_line_pointer != ',')
    {
      as_bad (_("expected comma after symbol name"));
      ignore_rest_of_line ();
      return;
    }

  input_line_pointer++;
  if ((size = get_absolute_expression ()) < 0)
    {
      as_warn (_("invalid length for .scomm directive"));
      ignore_rest_of_line ();
      return;
    }

  if (!get_and_validate_alignment (&align_val, &align_log2))
    {
      ignore_rest_of_line ();
      return;
    }

  *delimiter_ptr = 0;
  symbolP = symbol_find_or_make (name);
  *delimiter_ptr = delimiter_char;

  if (S_IS_DEFINED (symbolP))
    {
      as_bad (_("attempt to re-define symbol `%s'"),
	      S_GET_NAME (symbolP));
      ignore_rest_of_line ();
      return;
    }

  valueT current_symbol_value = S_GET_VALUE (symbolP);
  if (current_symbol_value && current_symbol_value != (valueT) size)
    {
      as_bad (_("attempt to redefine `%s' with a different length"),
	      S_GET_NAME (symbolP));
      ignore_rest_of_line ();
      return;
    }

  if (symbol_get_obj (symbolP)->local)
    {
      handle_local_scomm_symbol (symbolP, size, align_log2);
    }
  else
    {
      S_SET_VALUE (symbolP, size);
      S_SET_ALIGN (symbolP, 1 << align_log2);
      S_SET_EXTERNAL (symbolP);
      S_SET_SEGMENT (symbolP, &scom_section);
    }

  symbol_get_bfdsym (symbolP)->flags |= BSF_OBJECT;

  demand_empty_rest_of_line ();
}

/* Track for each attribute whether it has been set explicitly (and so
   should not have a default value set by the assembler).  */
static bool tic6x_attributes_set_explicitly[NUM_KNOWN_OBJ_ATTRIBUTES];

/* Parse a .c6xabi_attribute directive.  */

static void
s_tic6x_c6xabi_attribute (int ignored ATTRIBUTE_UNUSED)
{
  int tag = obj_elf_vendor_attribute (OBJ_ATTR_PROC);

  if (tag >= 0 && tag < NUM_KNOWN_OBJ_ATTRIBUTES)
    {
      tic6x_attributes_set_explicitly[tag] = true;
    }
}

typedef struct
{
  const char *name;
  int tag;
} tic6x_attribute_table;

static const tic6x_attribute_table tic6x_attributes[] =
  {
#define TAG(tag, value) { #tag, tag },
#include "elf/tic6x-attrs.h"
#undef TAG
  };

/* Convert an attribute name to a number.  */

int
tic6x_convert_symbolic_attribute (const char *name)
{
  if (name == NULL)
    {
      return -1;
    }

  unsigned int i;

  for (i = 0; i < ARRAY_SIZE (tic6x_attributes); i++)
    {
      if (strcmp (name, tic6x_attributes[i].name) == 0)
        {
          return tic6x_attributes[i].tag;
        }
    }

  return -1;
}

const pseudo_typeS md_pseudo_table[] =
  {
    { "arch", s_tic6x_arch, 0 },
    { "c6xabi_attribute", s_tic6x_c6xabi_attribute, 0 },
    { "nocmp", s_tic6x_nocmp, 0 },
    { "scomm",	s_tic6x_scomm, 0 },
    { "word", cons, 4 },
    { "ehtype", s_tic6x_ehtype, 0 },
    { "endp", s_tic6x_endp, 0 },
    { "handlerdata", s_tic6x_handlerdata, 0 },
    { "personalityindex", s_tic6x_personalityindex, 0 },
    { "personality", s_tic6x_personality, 0 },
    { "cantunwind", s_tic6x_cantunwind, 0 },
    { 0, 0, 0 }
  };

/* Hash table of opcodes.  For each opcode name, this stores a pointer
   to a tic6x_opcode_list listing (in an arbitrary order) all opcode
   table entries with that name.  */
static htab_t opcode_hash;

/* Initialize the assembler (called once at assembler startup).  */

void
md_begin (void)
{
  tic6x_opcode_id id;
  flagword applicable;
  segT original_seg;
  subsegT original_subseg;

  bfd_set_arch_mach (stdoutput, TARGET_ARCH, 0);

  opcode_hash = str_htab_create ();
  if (opcode_hash == NULL)
    {
      fatal_error("Failed to create opcode hash table.");
    }

  for (id = 0; id < tic6x_opcode_max; id++)
    {
      tic6x_opcode_list *opc = XNEW (tic6x_opcode_list);
      if (opc == NULL)
        {
          fatal_error("Failed to allocate memory for tic6x_opcode_list.");
        }

      opc->id = id;
      opc->next = str_hash_find (opcode_hash, tic6x_opcode_table[id].name);
      if (str_hash_insert (opcode_hash, tic6x_opcode_table[id].name, opc, 1) == NULL)
        {
          // Assuming fatal_error terminates the program, preventing memory leaks
          // and further use of an invalid hash table state.
          fatal_error("Failed to insert opcode into hash table.");
        }
    }

  original_seg = now_seg;
  original_subseg = now_subseg;

  sbss_section = subseg_new (".bss", 0);
  if (sbss_section == NULL)
    {
      fatal_error("Failed to create .sbss section.");
    }

  asection *sbss_section_info = seg_info(sbss_section);
  if (sbss_section_info == NULL)
    {
      fatal_error("Failed to get information for .sbss section after creation.");
    }
  sbss_section_info->bss = 1;

  applicable = bfd_applicable_section_flags (stdoutput);
  bfd_set_section_flags (sbss_section, applicable & SEC_ALLOC);

  subseg_set (original_seg, original_subseg);

  if (bfd_com_section_ptr == NULL)
    {
      fatal_error("bfd_com_section_ptr is uninitialized.");
    }
  if (bfd_com_section_ptr->symbol == NULL)
    {
      fatal_error("bfd_com_section_ptr->symbol is uninitialized.");
    }

  scom_section                = *bfd_com_section_ptr;
  scom_section.name           = ".scommon";
  scom_section.output_section = & scom_section;
  scom_section.symbol         = & scom_symbol;

  scom_symbol                 = * bfd_com_section_ptr->symbol;
  scom_symbol.name            = ".scommon";
  scom_symbol.section         = & scom_section;
}

/* Whether the current line being parsed had the "||" parallel bars.  */
static bool tic6x_line_parallel;

/* Whether the current line being parsed started "||^" to indicate an
   SPMASKed parallel instruction.  */
static bool tic6x_line_spmask;

/* If the current line being parsed had an instruction predicate, the
   creg value for that predicate (which must be nonzero); otherwise
   0.  */
static unsigned int tic6x_line_creg;

/* If the current line being parsed had an instruction predicate, the
   z value for that predicate; otherwise 0.  */
static unsigned int tic6x_line_z;

/* Return 1 (updating input_line_pointer as appropriate) if the line
   starting with C (immediately before input_line_pointer) starts with
   pre-opcode text appropriate for this target, 0 otherwise.  */

int
tic6x_unrecognized_line (int c)
{
  switch (c)
    {
    case '|':
      if (input_line_pointer[0] == '|')
	{
	  if (tic6x_line_parallel)
	    {
	      as_bad (_("multiple '||' on same line"));
	    }
	  if (tic6x_line_creg)
	    {
	      as_bad (_("'||' after predicate"));
	    }

	  if (input_line_pointer[1] == '^')
	    {
	      tic6x_line_spmask = true;
	      input_line_pointer += 2;
	    }
	  else
	    {
	      input_line_pointer += 1;
	    }
	  tic6x_line_parallel = true;
	  return 1;
	}
      return 0;

    case '[':
      {
	char *predicate_content_start = input_line_pointer;
	char *current_scan_ptr = input_line_pointer;
	char *closing_bracket_ptr = NULL;

	// Scan to find the closing ']' or end of statement.
	// `is_end_of_stmt` should handle the null terminator `\0`.
	while (!is_end_of_stmt (*current_scan_ptr))
	  {
	    if (*current_scan_ptr == ']')
	      {
		closing_bracket_ptr = current_scan_ptr;
		break;
	      }
	    current_scan_ptr++;
	  }

	if (closing_bracket_ptr == NULL)
	  {
	    return 0; // No closing ']' found, not a recognized predicate format.
	  }

	// Report error if multiple predicates are on the same line.
	// The original code proceeds to parse the current predicate even after this error.
	if (tic6x_line_creg)
	  {
	    as_bad (_("multiple predicates on same line"));
	  }

	// Reset scan pointer to start of predicate content for detailed parsing.
	current_scan_ptr = predicate_content_start;

	unsigned int temp_z = 0;
	bool temp_areg = false;
	int temp_reg_num = -1;
	bool predicate_is_bad = false;

	// Parse '!' (NOT) prefix.
	if (*current_scan_ptr == '!')
	  {
	    temp_z = 1;
	    current_scan_ptr++;
	  }

	// Parse register bank (A or B, case-insensitive).
	if (*current_scan_ptr == 'A' || *current_scan_ptr == 'a')
	  {
	    temp_areg = true;
	  }
	else if (*current_scan_ptr == 'B' || *current_scan_ptr == 'b')
	  {
	    temp_areg = false;
	  }
	else
	  {
	    predicate_is_bad = true;
	  }

	if (!predicate_is_bad)
	  {
	    current_scan_ptr++; // Move past 'A' or 'B'.

	    // Parse register number (0, 1, or 2).
	    if (*current_scan_ptr >= '0' && *current_scan_ptr <= '2')
	      {
		temp_reg_num = *current_scan_ptr - '0';
	      }
	    else
	      {
		predicate_is_bad = true;
	      }
	  }

	// Check if the character immediately after the digit is the closing ']',
	// ensuring no extra characters within the predicate.
	if (!predicate_is_bad)
	  {
	    current_scan_ptr++; // Move past the digit.
	    if (current_scan_ptr != closing_bracket_ptr)
	      {
		predicate_is_bad = true;
	      }
	  }

	// If the predicate syntax is invalid, report error and advance input_line_pointer.
	if (predicate_is_bad)
	  {
	    // Temporarily null-terminate the string for `as_bad` to print the full bad predicate,
	    // including the leading '['. `predicate_content_start - 1` points to the '['.
	    char temp_char = closing_bracket_ptr[1];
	    closing_bracket_ptr[1] = '\0';
	    as_bad (_("bad predicate '%s'"), predicate_content_start - 1);
	    closing_bracket_ptr[1] = temp_char; // Restore original character.

	    input_line_pointer = closing_bracket_ptr + 1; // Advance past the ']'
	    return 1;
	  }

	// If the predicate is valid, update global state variables and advance input_line_pointer.
	input_line_pointer = closing_bracket_ptr + 1;
	tic6x_line_z = temp_z;

	switch (temp_reg_num)
	  {
	  case 0:
	    tic6x_line_creg = (temp_areg ? 6 : 1);
	    if (temp_areg && !tic6x_predicate_a0)
	      {
		as_bad (_("predication on A0 not supported on this architecture"));
	      }
	    break;

	  case 1:
	    tic6x_line_creg = (temp_areg ? 4 : 2);
	    break;

	  case 2:
	    tic6x_line_creg = (temp_areg ? 5 : 3);
	    break;

	  default:
	    // This case should logically be unreachable if `predicate_is_bad` handling is correct,
	    // as `temp_reg_num` would only be 0, 1, or 2 at this point.
	    // It serves as an assertion for internal logic consistency.
	    abort ();
	  }
	return 1;
      }

    default:
      return 0;
    }
}

/* Do any target-specific handling of a label required.  */

static void
tic6x_reset_parallel_state (void)
{
  tic6x_line_parallel = false;
  tic6x_line_spmask = false;
}

static void
tic6x_reset_predicate_state (void)
{
  tic6x_line_creg = 0;
  tic6x_line_z = 0;
}

void
tic6x_frob_label (symbolS *sym)
{
  segment_info_type *si;
  tic6x_label_list *old_label_list;
  tic6x_label_list *new_label_node;

  if (tic6x_line_parallel)
    {
      as_bad (_("label after '||'"));
      tic6x_reset_parallel_state ();
    }
  if (tic6x_line_creg)
    {
      as_bad (_("label after predicate"));
      tic6x_reset_predicate_state ();
    }

  si = seg_info (now_seg);
  old_label_list = si->tc_segment_info_data.label_list;

  new_label_node = XNEW (tic6x_label_list);

  new_label_node->next = old_label_list;
  new_label_node->label = sym;
  si->tc_segment_info_data.label_list = new_label_node;

  dwarf2_emit_label (sym);
}

/* At end-of-line, give errors for start-of-line decorations that
   needed an instruction but were not followed by one.  */

static void
handle_tic6x_parallel_error (void)
{
  as_bad (_("'||' not followed by instruction"));
  tic6x_line_parallel = false;
  tic6x_line_spmask = false;
}

static void
handle_tic6x_predicate_error (void)
{
  as_bad (_("predicate not followed by instruction"));
  tic6x_line_creg = 0;
  tic6x_line_z = 0;
}

static void
tic6x_end_of_line (void)
{
  if (tic6x_line_parallel)
    {
      handle_tic6x_parallel_error ();
    }
  if (tic6x_line_creg)
    {
      handle_tic6x_predicate_error ();
    }
}

/* Do any target-specific handling of the start of a logical line.  */

inline void
tic6x_start_line_hook (void)
{
  tic6x_end_of_line ();
}

/* Do target-specific handling immediately after an input file from
   the command line, and any other inputs it includes, have been
   read.  */

void
tic6x_cleanup (void)
{
  (void)tic6x_end_of_line ();
}

/* Do target-specific initialization after arguments have been
   processed and the output file created.  */

#include <stdio.h>

void
tic6x_init_after_args (void)
{
  // Assume elf32_tic6x_set_use_rela_p returns an int to indicate success or failure.
  // This is a common pattern in C, and ignoring such a return value is a SonarCloud code smell (S2632).
  // If the function actually returns void, this refactoring would be unnecessary,
  // as the original code would already be optimal for this simple operation.
  int result = elf32_tic6x_set_use_rela_p(stdoutput, tic6x_generate_rela);

  // For improved reliability and maintainability, check the return value.
  // Assuming 0 indicates success and any non-zero value indicates an error.
  if (result != 0)
  {
    // Log the error to standard error. This provides crucial information for
    // debugging and monitoring without altering the external signature or
    // behavior (return value) of tic6x_init_after_args.
    // Logging is a standard approach to handle errors in void functions that
    // cannot propagate errors back to their callers.
    fprintf(stderr, "ERROR: tic6x_init_after_args: Failed to set use_rela_p (error code: %d).\n", result);
  }
}

/* Free LIST of labels (possibly NULL).  */

static void
tic6x_free_label_list (tic6x_label_list *list)
{
  tic6x_label_list *current_node = list;
  tic6x_label_list *next_node;

  while (current_node != NULL)
    {
      next_node = current_node->next;
      free(current_node);
      current_node = next_node;
    }
}

/* Handle a data alignment of N bytes.  */

void
tic6x_cons_align (int n ATTRIBUTE_UNUSED)
{
  segment_info_type *seginfo = seg_info (now_seg);

  if (seginfo == NULL)
    {
      return;
    }

  tic6x_free_label_list (seginfo->tc_segment_info_data.label_list);
  seginfo->tc_segment_info_data.label_list = NULL;
  seginfo->tc_segment_info_data.execute_packet_frag = NULL;
  seginfo->tc_segment_info_data.last_insn_lsb = NULL;
  seginfo->tc_segment_info_data.spmask_addr = NULL;
  seginfo->tc_segment_info_data.func_units_used = 0;
}

/* Handle an alignment directive.  Return TRUE if the
   machine-independent frag generation should be skipped.  */

bool
tic6x_do_align(int n, char *fill, int len ATTRIBUTE_UNUSED, int max)
{
    const int max_handled_n_value = 5;
    const int frag_buffer_alloc_size = 32;

    if (n <= 0 || n > max_handled_n_value) {
        return false;
    }

    if (max < 0 || max >= (1 << n)) {
        return false;
    }

    if (need_pass_2) {
        return false;
    }

    if (fill != NULL) {
        return false;
    }

    if (!subseg_text_p(now_seg)) {
        return false;
    }

    if (frag_now_fix() != 0) {
        if (frag_now->fr_type != rs_machine_dependent) {
            frag_wane(frag_now);
        }
        frag_new(0);
    }

    frag_grow(frag_buffer_alloc_size);

    fragS *current_align_frag = frag_now;

    char *returned_literal_ptr = frag_var(rs_machine_dependent,
                                          frag_buffer_alloc_size,
                                          frag_buffer_alloc_size,
                                          max,
                                          NULL,
                                          n,
                                          NULL);

    if (returned_literal_ptr != current_align_frag->fr_literal) {
        abort();
    }

    current_align_frag->tc_frag_data.is_insns = false;

    return true;
}

/* Types of operand for parsing purposes.  These are used as bit-masks
   to tell tic6x_parse_operand what forms of operand are
   permitted.  */
#define TIC6X_OP_EXP		0x0001u
#define TIC6X_OP_REG		0x0002u
#define TIC6X_OP_REGPAIR	0x0004u
#define TIC6X_OP_IRP		0x0008u
#define TIC6X_OP_NRP		0x0010u
/* With TIC6X_OP_MEM_NOUNREG, the contents of a () offset are always
   interpreted as an expression, which may be a symbol with the same
   name as a register that ends up being implicitly DP-relative.  With
   TIC6X_OP_MEM_UNREG, the contents of a () offset are interpreted as
   a register if they match one, and failing that as an expression,
   which must be constant.  */
#define TIC6X_OP_MEM_NOUNREG	0x0020u
#define TIC6X_OP_MEM_UNREG	0x0040u
#define TIC6X_OP_CTRL		0x0080u
#define TIC6X_OP_FUNC_UNIT	0x0100u

/* A register or register pair read by the assembler.  */
typedef struct
{
  /* The side the register is on (1 or 2).  */
  unsigned int side;
  /* The register number (0 to 31).  */
  unsigned int num;
} tic6x_register;

/* Types of modification of a base address.  */
typedef enum
  {
    tic6x_mem_mod_none,
    tic6x_mem_mod_plus,
    tic6x_mem_mod_minus,
    tic6x_mem_mod_preinc,
    tic6x_mem_mod_predec,
    tic6x_mem_mod_postinc,
    tic6x_mem_mod_postdec
  } tic6x_mem_mod;

/* Scaled [] or unscaled () nature of an offset.  */
typedef enum
  {
    tic6x_offset_none,
    tic6x_offset_scaled,
    tic6x_offset_unscaled
  } tic6x_mem_scaling;

/* A memory operand read by the assembler.  */
typedef struct
{
  /* The base register.  */
  tic6x_register base_reg;
  /* How the base register is modified.  */
  tic6x_mem_mod mod;
  /* Whether there is an offset (required with plain "+" and "-"), and
     whether it is scaled or unscaled if so.  */
  tic6x_mem_scaling scaled;
  /* Whether the offset is a register (TRUE) or an expression
     (FALSE).  */
  bool offset_is_reg;
  /* The offset.  */
  union
  {
    expressionS exp;
    tic6x_register reg;
  } offset;
} tic6x_mem_ref;

/* A functional unit in SPMASK operands read by the assembler.  */
typedef struct
{
  /* The basic unit.  */
  tic6x_func_unit_base base;
  /* The side (1 or 2).  */
  unsigned int side;
} tic6x_func_unit_operand;

/* An operand read by the assembler.  */
typedef struct
{
  /* The syntactic form of the operand, as one of the bit-masks
     above.  */
  unsigned int form;
  /* The operand value.  */
  union
  {
    /* An expression: TIC6X_OP_EXP.  */
    expressionS exp;
    /* A register: TIC6X_OP_REG, TIC6X_OP_REGPAIR.  */
    tic6x_register reg;
    /* A memory reference: TIC6X_OP_MEM_NOUNREG,
       TIC6X_OP_MEM_UNREG.  */
    tic6x_mem_ref mem;
    /* A control register: TIC6X_OP_CTRL.  */
    tic6x_ctrl_id ctrl;
    /* A functional unit: TIC6X_OP_FUNC_UNIT.  */
    tic6x_func_unit_operand func_unit;
  } value;
} tic6x_operand;

#define skip_whitespace(str)  do { if (is_whitespace (*(str))) ++(str); } while (0)

/* Parse a register operand, or part of an operand, starting at *P.
   If syntactically OK (including that the number is in the range 0 to
   31, but not necessarily in range for this architecture), return
   TRUE, putting the register side and number in *REG and update *P to
   point immediately after the register number; otherwise return FALSE
   without changing *P (but possibly changing *REG).  Do not print any
   diagnostics.  */

static bool
tic6x_parse_register (char **p, tic6x_register *reg)
{
  if (p == NULL || *p == NULL || reg == NULL)
    {
      return false;
    }

  const char *current_pos = *p;
  int parsed_num = 0;

  char side_char = *current_pos;
  if (side_char == 'a' || side_char == 'A')
    {
      reg->side = 1;
    }
  else if (side_char == 'b' || side_char == 'B')
    {
      reg->side = 2;
    }
  else
    {
      return false;
    }
  current_pos++;

  if (*current_pos < '0' || *current_pos > '9')
    {
      return false;
    }
  parsed_num = *current_pos - '0';
  current_pos++;

  if (parsed_num > 0 && *current_pos >= '0' && *current_pos <= '9')
    {
      parsed_num = parsed_num * 10 + (*current_pos - '0');
      current_pos++;
    }

  if (*current_pos >= '0' && *current_pos <= '9')
    {
      return false;
    }

  if (parsed_num > 31)
    {
      return false;
    }

  reg->num = parsed_num;
  *p = (char *)current_pos;
  return true;
}

/* Parse the initial two characters of a functional unit name starting
   at *P.  If OK, set *BASE and *SIDE and return true; otherwise,
   return FALSE.  */

static bool
tic6x_parse_func_unit_base (char *p, tic6x_func_unit_base *base,
			    unsigned int *side)
{
  if (p == NULL || strlen(p) < 2)
    {
      return false;
    }

  tic6x_func_unit_base local_base;
  unsigned int local_side;

  switch (tolower((unsigned char)p[0]))
    {
    case 'd':
      local_base = tic6x_func_unit_d;
      break;
    case 'l':
      local_base = tic6x_func_unit_l;
      break;
    case 'm':
      local_base = tic6x_func_unit_m;
      break;
    case 's':
      local_base = tic6x_func_unit_s;
      break;
    default:
      return false;
    }

  switch (p[1])
    {
    case '1':
      local_side = 1;
      break;
    case '2':
      local_side = 2;
      break;
    default:
      return false;
    }

  *base = local_base;
  *side = local_side;

  return true;
}

/* Parse an operand starting at *P.  If the operand parses OK, return
   TRUE and store the value in *OP; otherwise return FALSE (possibly
   changing *OP).  In any case, update *P to point to the following
   comma or end of line.  The possible operand forms are given by
   OP_FORMS.  For diagnostics, this is operand OPNO of an opcode
   starting at STR, length OPC_LEN.  */

static bool
check_terminator_and_advance(char **p_ptr)
{
  skip_whitespace(*p_ptr);
  if (is_end_of_stmt(**p_ptr) || **p_ptr == ',')
    {
      return true;
    }
  return false;
}

static bool
parse_keyword_operand(char **p_ptr, const char *keyword, tic6x_operand *op, tic6x_operand_form form)
{
  char *q = *p_ptr;
  size_t len = strlen(keyword);

  if (strncasecmp(q, keyword, len) == 0)
    {
      char *rq = q + len;
      if (check_terminator_and_advance(&rq))
        {
          op->form = form;
          *p_ptr = rq;
          return true;
        }
    }
  return false;
}

static bool
parse_func_unit_operand(char **p_ptr, tic6x_operand *op)
{
  char *q = *p_ptr;
  tic6x_func_unit_base base;
  unsigned int side;

  if (tic6x_parse_func_unit_base(q, &base, &side))
    {
      char *rq = q + 2; 
      if (check_terminator_and_advance(&rq))
        {
          op->form = TIC6X_OP_FUNC_UNIT;
          op->value.func_unit.base = base;
          op->value.func_unit.side = side;
          *p_ptr = rq;
          return true;
        }
    }
  return false;
}

static bool
parse_ctrl_operand(char **p_ptr, tic6x_operand *op, unsigned int opno, int opc_len, char *str)
{
  char *q = *p_ptr;
  tic6x_ctrl_id crid;

  for (crid = 0; crid < tic6x_ctrl_max; crid++)
    {
      size_t len = strlen(tic6x_ctrl_table[crid].name);

      if (strncasecmp(tic6x_ctrl_table[crid].name, q, len) == 0)
        {
          char *rq = q + len;
          if (check_terminator_and_advance(&rq))
            {
              op->form = TIC6X_OP_CTRL;
              op->value.ctrl = crid;
              *p_ptr = rq;
              if (!(tic6x_ctrl_table[crid].isa_variants & tic6x_features))
                {
                  as_bad(_("control register '%s' not supported "
                           "on this architecture"),
                         tic6x_ctrl_table[crid].name);
                }
              return true;
            }
        }
    }
  return false;
}

static bool
validate_register_support(const tic6x_register *reg)
{
  if (reg->num >= tic6x_num_registers)
    {
      as_bad(_("register number %u not supported on this architecture"), reg->num);
      return false;
    }
  return true;
}

static bool
parse_register_or_pair_operand(char **p_ptr, tic6x_operand *op, unsigned int op_forms,
                               unsigned int opno, int opc_len, char *str)
{
  char *rq = *p_ptr;
  tic6x_register first_reg = {0};
  tic6x_register second_reg = {0};
  bool reg_ok = tic6x_parse_register(&rq, &first_reg);

  if (!reg_ok)
    {
      return false;
    }

  if (*rq == ':' && (op_forms & TIC6X_OP_REGPAIR))
    {
      char *next_rq = rq + 1;
      reg_ok = tic6x_parse_register(&next_rq, &second_reg);
      if (reg_ok && check_terminator_and_advance(&next_rq))
        {
          if ((second_reg.num & 1)
              || (first_reg.num != second_reg.num + 1)
              || (first_reg.side != second_reg.side))
            {
              as_bad(_("register pair for operand %u of '%.*s' not a valid even/odd pair"),
                     opno, opc_len, str);
              return false;
            }
          op->form = TIC6X_OP_REGPAIR;
          op->value.reg = second_reg;
          *p_ptr = next_rq;

          validate_register_support(&first_reg);
          validate_register_support(&second_reg);
          return true;
        }
    }
  else if (op_forms & TIC6X_OP_REG)
    {
      if (check_terminator_and_advance(&rq))
        {
          op->form = TIC6X_OP_REG;
          op->value.reg = first_reg;
          *p_ptr = rq;

          validate_register_support(&first_reg);
          return true;
        }
    }
  return false;
}

static bool
parse_mem_operand_internal(char **p_ptr, tic6x_operand *op, unsigned int op_forms)
{
  char *mq = *p_ptr;
  tic6x_mem_mod mem_mod = tic6x_mem_mod_none;
  tic6x_register base_reg = {0};
  bool require_offset, permit_offset;
  tic6x_mem_scaling scaled = tic6x_offset_none;
  bool offset_is_reg = false;
  expressionS offset_exp = {0};
  tic6x_register offset_reg = {0};

  if (*mq == '*')
    mq++;
  else
    return false;

  skip_whitespace(mq);
  if (*mq == '+')
    {
      if (mq[1] == '+') { mem_mod = tic6x_mem_mod_preinc; mq += 2; }
      else { mem_mod = tic6x_mem_mod_plus; mq++; }
    }
  else if (*mq == '-')
    {
      if (mq[1] == '-') { mem_mod = tic6x_mem_mod_predec; mq += 2; }
      else { mem_mod = tic6x_mem_mod_minus; mq++; }
    }

  skip_whitespace(mq);
  if (!tic6x_parse_register(&mq, &base_reg))
    return false;

  if (mem_mod == tic6x_mem_mod_none)
    {
      skip_whitespace(mq);
      if (mq[0] == '+' && mq[1] == '+') { mem_mod = tic6x_mem_mod_postinc; mq += 2; }
      else if (mq[0] == '-' && mq[1] == '-') { mem_mod = tic6x_mem_mod_postdec; mq += 2; }
    }

  permit_offset = (mem_mod != tic6x_mem_mod_none);
  require_offset = (mem_mod == tic6x_mem_mod_plus || mem_mod == tic6x_mem_mod_minus);

  if (permit_offset)
    {
      char endc = 0;
      skip_whitespace(mq);
      if (*mq == '[') { scaled = tic6x_offset_scaled; mq++; endc = ']'; }
      else if (*mq == '(') { scaled = tic6x_offset_unscaled; mq++; endc = ')'; }

      if (scaled != tic6x_offset_none)
        {
          skip_whitespace(mq);
          bool potential_reg_offset = (scaled == tic6x_offset_scaled || (op_forms & TIC6X_OP_MEM_UNREG));
          char *rq_temp = mq;

          if (potential_reg_offset && tic6x_parse_register(&rq_temp, &offset_reg))
            {
              skip_whitespace(rq_temp);
              if (*rq_temp == endc)
                {
                  mq = rq_temp;
                  offset_is_reg = true;
                }
            }

          if (!offset_is_reg)
            {
              char *save_input_line_pointer = input_line_pointer;
              input_line_pointer = mq;
              expression(&offset_exp);
              mq = input_line_pointer;
              input_line_pointer = save_input_line_pointer;
            }
          skip_whitespace(mq);
          if (*mq != endc)
            return false;
          mq++;
        }
    }

  if (require_offset && scaled == tic6x_offset_none)
    return false;

  if (!check_terminator_and_advance(&mq))
    return false;

  op->form = op_forms & (TIC6X_OP_MEM_NOUNREG | TIC6X_OP_MEM_UNREG);
  op->value.mem.base_reg = base_reg;
  op->value.mem.mod = mem_mod;
  op->value.mem.scaled = scaled;
  op->value.mem.offset_is_reg = offset_is_reg;
  if (offset_is_reg)
    op->value.mem.offset.reg = offset_reg;
  else
    op->value.mem.offset.exp = offset_exp;
  *p_ptr = mq;

  validate_register_support(&base_reg);
  if (offset_is_reg)
    validate_register_support(&offset_reg);

  return true;
}

static void
parse_expression_operand(char **p_ptr, tic6x_operand *op)
{
  char *save_input_line_pointer;

  save_input_line_pointer = input_line_pointer;
  input_line_pointer = *p_ptr;
  op->form = TIC6X_OP_EXP;
  expression(&op->value.exp);
  *p_ptr = input_line_pointer;
  input_line_pointer = save_input_line_pointer;
}

static void
report_final_parse_error(unsigned int op_forms, unsigned int opno, int opc_len, char *str)
{
  switch (op_forms)
    {
    case TIC6X_OP_REG | TIC6X_OP_REGPAIR:
      as_bad(_("bad register or register pair for operand %u of '%.*s'"), opno, opc_len, str);
      break;
    case TIC6X_OP_REG | TIC6X_OP_CTRL:
    case TIC6X_OP_REG:
      as_bad(_("bad register for operand %u of '%.*s'"), opno, opc_len, str);
      break;
    case TIC6X_OP_REGPAIR:
      as_bad(_("bad register pair for operand %u of '%.*s'"), opno, opc_len, str);
      break;
    case TIC6X_OP_FUNC_UNIT:
      as_bad(_("bad functional unit for operand %u of '%.*s'"), opno, opc_len, str);
      break;
    default:
      as_bad(_("bad operand %u of '%.*s'"), opno, opc_len, str);
      break;
    }
}

static void
advance_past_junk(char **p_ptr)
{
  char *q = *p_ptr;
  while (!is_end_of_stmt(*q) && *q != ',')
    q++;
  *p_ptr = q;
}

static bool
tic6x_parse_operand (char **p, tic6x_operand *op, unsigned int op_forms,
		     char *str, int opc_len, unsigned int opno)
{
  char *q = *p;
  bool parsed_successfully = false;

  if ((op_forms & (TIC6X_OP_MEM_NOUNREG | TIC6X_OP_MEM_UNREG))
      == (TIC6X_OP_MEM_NOUNREG | TIC6X_OP_MEM_UNREG))
    {
      as_bad (_("Internal error: both TIC6X_OP_MEM_NOUNREG and "
                "TIC6X_OP_MEM_UNREG flags set for operand %u"), opno);
      advance_past_junk(&q);
      *p = q;
      return false;
    }

  if ((op_forms & TIC6X_OP_FUNC_UNIT) && parse_func_unit_operand(&q, op))
    {
      parsed_successfully = true;
    }
  else if ((op_forms & TIC6X_OP_IRP) && parse_keyword_operand(&q, "irp", op, TIC6X_OP_IRP))
    {
      parsed_successfully = true;
    }
  else if ((op_forms & TIC6X_OP_NRP) && parse_keyword_operand(&q, "nrp", op, TIC6X_OP_NRP))
    {
      parsed_successfully = true;
    }
  else if ((op_forms & TIC6X_OP_CTRL) && parse_ctrl_operand(&q, op, opno, opc_len, str))
    {
      parsed_successfully = true;
    }
  else if ((op_forms & (TIC6X_OP_MEM_NOUNREG | TIC6X_OP_MEM_UNREG)) &&
           parse_mem_operand_internal(&q, op, op_forms))
    {
      parsed_successfully = true;
    }
  else if ((op_forms & (TIC6X_OP_REG | TIC6X_OP_REGPAIR)) &&
           parse_register_or_pair_operand(&q, op, op_forms, opno, opc_len, str))
    {
      parsed_successfully = true;
    }
  else if ((op_forms & TIC6X_OP_EXP))
    {
      parse_expression_operand(&q, op);
      parsed_successfully = true;
    }

  if (parsed_successfully)
    {
      skip_whitespace(q);
      if (!is_end_of_stmt(*q) && *q != ',')
        {
          as_bad (_("junk after operand %u of '%.*s'"), opno, opc_len, str);
          advance_past_junk(&q);
          *p = q;
          return false;
        }
    }
  else
    {
      report_final_parse_error(op_forms, opno, opc_len, str);
      advance_past_junk(&q);
      *p = q;
      return false;
    }

  *p = q;
  return true;
}

/* Table of assembler operators and associated O_* values.  */
typedef struct
{
  const char *name;
  operatorT op;
} tic6x_operator_table;
static const tic6x_operator_table tic6x_operators[] = {
#define O_dsbt_index O_md1
  { "dsbt_index", O_dsbt_index },
#define O_got O_md2
  { "got", O_got },
#define O_dpr_got O_md3
  { "dpr_got", O_dpr_got },
#define O_dpr_byte O_md4
  { "dpr_byte", O_dpr_byte },
#define O_dpr_hword O_md5
  { "dpr_hword", O_dpr_hword },
#define O_dpr_word O_md6
  { "dpr_word", O_dpr_word },
#define O_pcr_offset O_md7
  { "pcr_offset", O_pcr_offset }
};

/* Parse a name in some machine-specific way.  Used on C6X to handle
   assembler operators.  */

int
tic6x_parse_name (const char *name, expressionS *exprP,
		  enum expr_mode mode ATTRIBUTE_UNUSED, char *nextchar)
{
  char *current_parse_pos = input_line_pointer;
  char *name_start, *name_end;
  const char *inner_name;
  unsigned int i;
  operatorT op = O_illegal;
  symbolS *sym, *op_sym = NULL;

  if (*name != '$')
    return 0;

  for (i = 0; i < ARRAY_SIZE (tic6x_operators); i++)
    if (strcasecmp (name + 1, tic6x_operators[i].name) == 0)
      {
	op = tic6x_operators[i].op;
	break;
      }

  if (op == O_illegal)
    return 0;

  char saved_nextchar_val = *nextchar;
  *input_line_pointer = saved_nextchar_val;
  skip_whitespace (current_parse_pos);

  if (*current_parse_pos != '(')
    goto fail_parse;
  current_parse_pos++;
  skip_whitespace (current_parse_pos);

  if (!is_name_beginner (*current_parse_pos))
    goto fail_parse;

  name_start = current_parse_pos;
  current_parse_pos++;
  while (is_part_of_name (*current_parse_pos))
    current_parse_pos++;
  name_end = current_parse_pos;
  skip_whitespace (current_parse_pos);

  if (op == O_pcr_offset)
    {
      if (*current_parse_pos != ',')
	goto fail_parse;
      current_parse_pos++;
      skip_whitespace (current_parse_pos);

      if (!is_name_beginner (*current_parse_pos))
	goto fail_parse;

      char *op_name_start_local = current_parse_pos;
      current_parse_pos++;
      while (is_part_of_name (*current_parse_pos))
	current_parse_pos++;
      char *op_name_end_local = current_parse_pos;
      skip_whitespace (current_parse_pos);

      char saved_char_op_name = *op_name_end_local;
      *op_name_end_local = '\0';
      op_sym = symbol_find_or_make (op_name_start_local);
      *op_name_end_local = saved_char_op_name;
    }

  if (*current_parse_pos != ')')
    goto fail_parse;

  input_line_pointer = current_parse_pos + 1;
  *nextchar = *input_line_pointer;
  *input_line_pointer = '\0';

  char saved_char_name = *name_end;
  *name_end = '\0';
  inner_name = name_start;

  if (op == O_dsbt_index && strcmp (inner_name, "__c6xabi_DSBT_BASE") != 0)
    {
      as_bad (_("$DSBT_INDEX must be used with __c6xabi_DSBT_BASE"));
      inner_name = "__c6xabi_DSBT_BASE";
    }
  sym = symbol_find_or_make (inner_name);
  *name_end = saved_char_name;

  exprP->X_op = op;
  exprP->X_add_symbol = sym;
  exprP->X_add_number = 0;
  exprP->X_op_symbol = op_sym;
  exprP->X_md = 0;

  return 1;

fail_parse:
  *input_line_pointer = '\0';
  return 0;
}

/* Create a fixup for an expression.  Same arguments as fix_new_exp,
   plus FIX_ADDA which is TRUE for ADDA instructions (to indicate that
   fixes resolving to constants should have those constants implicitly
   shifted) and FALSE otherwise, but look for C6X-specific expression
   types and adjust the relocations or give errors accordingly.  */

static void
report_reloc_error (const char *msg)
{
  as_bad (msg);
}

static bfd_reloc_code_real_type
get_dsbt_index_reloc_type (bfd_reloc_code_real_type r_type)
{
  switch (r_type)
    {
    case BFD_RELOC_C6000_SBR_U15_W:
      return BFD_RELOC_C6000_DSBT_INDEX;
    default:
      report_reloc_error (_("$DSBT_INDEX not supported in this context"));
      return BFD_RELOC_UNUSED;
    }
}

static bfd_reloc_code_real_type
get_got_reloc_type (bfd_reloc_code_real_type r_type)
{
  switch (r_type)
    {
    case BFD_RELOC_C6000_SBR_U15_W:
      return BFD_RELOC_C6000_SBR_GOT_U15_W;
    default:
      report_reloc_error (_("$GOT not supported in this context"));
      return BFD_RELOC_UNUSED;
    }
}

static bfd_reloc_code_real_type
get_dpr_got_reloc_type (bfd_reloc_code_real_type r_type)
{
  switch (r_type)
    {
    case BFD_RELOC_C6000_ABS_L16:
      return BFD_RELOC_C6000_SBR_GOT_L16_W;
    case BFD_RELOC_C6000_ABS_H16:
      return BFD_RELOC_C6000_SBR_GOT_H16_W;
    default:
      report_reloc_error (_("$DPR_GOT not supported in this context"));
      return BFD_RELOC_UNUSED;
    }
}

static bfd_reloc_code_real_type
get_dpr_byte_reloc_type (bfd_reloc_code_real_type r_type)
{
  switch (r_type)
    {
    case BFD_RELOC_C6000_ABS_S16:
      return BFD_RELOC_C6000_SBR_S16;
    case BFD_RELOC_C6000_ABS_L16:
      return BFD_RELOC_C6000_SBR_L16_B;
    case BFD_RELOC_C6000_ABS_H16:
      return BFD_RELOC_C6000_SBR_H16_B;
    default:
      report_reloc_error (_("$DPR_BYTE not supported in this context"));
      return BFD_RELOC_UNUSED;
    }
}

static bfd_reloc_code_real_type
get_dpr_hword_reloc_type (bfd_reloc_code_real_type r_type)
{
  switch (r_type)
    {
    case BFD_RELOC_C6000_ABS_L16:
      return BFD_RELOC_C6000_SBR_L16_H;
    case BFD_RELOC_C6000_ABS_H16:
      return BFD_RELOC_C6000_SBR_H16_H;
    default:
      report_reloc_error (_("$DPR_HWORD not supported in this context"));
      return BFD_RELOC_UNUSED;
    }
}

static bfd_reloc_code_real_type
get_dpr_word_reloc_type (bfd_reloc_code_real_type r_type)
{
  switch (r_type)
    {
    case BFD_RELOC_C6000_ABS_L16:
      return BFD_RELOC_C6000_SBR_L16_W;
    case BFD_RELOC_C6000_ABS_H16:
      return BFD_RELOC_C6000_SBR_H16_W;
    default:
      report_reloc_error (_("$DPR_WORD not supported in this context"));
      return BFD_RELOC_UNUSED;
    }
}

static bfd_reloc_code_real_type
get_pcr_offset_reloc_type (bfd_reloc_code_real_type r_type)
{
  switch (r_type)
    {
    case BFD_RELOC_C6000_ABS_S16:
    case BFD_RELOC_C6000_ABS_L16:
      return BFD_RELOC_C6000_PCR_L16;
    case BFD_RELOC_C6000_ABS_H16:
      return BFD_RELOC_C6000_PCR_H16;
    default:
      report_reloc_error (_("$PCR_OFFSET not supported in this context"));
      return BFD_RELOC_UNUSED;
    }
}

static void
tic6x_fix_new_exp (fragS *frag, int where, int size, expressionS *exp,
		   int pcrel, bfd_reloc_code_real_type r_type,
		   bool fix_adda)
{
  bfd_reloc_code_real_type new_reloc = BFD_RELOC_UNUSED;
  symbolS *subsy = NULL;

  switch (exp->X_op)
    {
    case O_dsbt_index:
      new_reloc = get_dsbt_index_reloc_type (r_type);
      if (new_reloc == BFD_RELOC_UNUSED)
        return;
      break;

    case O_got:
      new_reloc = get_got_reloc_type (r_type);
      if (new_reloc == BFD_RELOC_UNUSED)
        return;
      break;

    case O_dpr_got:
      new_reloc = get_dpr_got_reloc_type (r_type);
      if (new_reloc == BFD_RELOC_UNUSED)
        return;
      break;

    case O_dpr_byte:
      new_reloc = get_dpr_byte_reloc_type (r_type);
      if (new_reloc == BFD_RELOC_UNUSED)
        return;
      break;

    case O_dpr_hword:
      new_reloc = get_dpr_hword_reloc_type (r_type);
      if (new_reloc == BFD_RELOC_UNUSED)
        return;
      break;

    case O_dpr_word:
      new_reloc = get_dpr_word_reloc_type (r_type);
      if (new_reloc == BFD_RELOC_UNUSED)
        return;
      break;

    case O_pcr_offset:
      subsy = exp->X_op_symbol;
      new_reloc = get_pcr_offset_reloc_type (r_type);
      if (new_reloc == BFD_RELOC_UNUSED)
        return;
      break;

    case O_symbol:
      /* No new_reloc specified for O_symbol, so original r_type will be used
         by fix_new_exp when new_reloc remains BFD_RELOC_UNUSED. */
      break;

    default:
      if (pcrel)
        {
          report_reloc_error (_("invalid PC-relative operand"));
          return;
        }
      /* For other default cases, new_reloc remains BFD_RELOC_UNUSED,
         leading to fix_new_exp. */
      break;
    }

  fixS *fix;
  if (new_reloc == BFD_RELOC_UNUSED)
    fix = fix_new_exp (frag, where, size, exp, pcrel, r_type);
  else
    fix = fix_new (frag, where, size, exp->X_add_symbol, exp->X_add_number,
		   pcrel, new_reloc);

  fix->tc_fix_data.fix_subsy = subsy;
  fix->tc_fix_data.fix_adda = fix_adda;
}

/* Generate a fix for a constant (.word etc.).  Needed to ensure these
   go through the error checking in tic6x_fix_new_exp.  */

void
tic6x_cons_fix_new (fragS *frag, int where, int size, expressionS *exp)
{
  bfd_reloc_code_real_type r_type_local;

  switch (size)
    {
    case 1:
      r_type_local = BFD_RELOC_8;
      break;

    case 2:
      r_type_local = BFD_RELOC_16;
      break;

    case 4:
      r_type_local = BFD_RELOC_32;
      break;

    default:
      as_bad (_("no %d-byte relocations available"), size);
      return;
    }

  tic6x_fix_new_exp (frag, where, size, exp, 0, r_type_local, false);
}

/* Initialize target-specific fix data.  */

void
tic6x_init_fix_data (fixS *fixP)
{
  if (fixP == NULL)
  {
    return;
  }
  fixP->tc_fix_data.fix_adda = false;
  fixP->tc_fix_data.fix_subsy = NULL;
}

/* Return true if the fix can be handled by GAS, false if it must
   be passed through to the linker.  */

bool
tic6x_fix_adjustable (fixS *fixP)
{
  switch (fixP->fx_r_type)
    {
    case BFD_RELOC_C6000_SBR_GOT_U15_W:
    case BFD_RELOC_C6000_SBR_GOT_H16_W:
    case BFD_RELOC_C6000_SBR_GOT_L16_W:
    case BFD_RELOC_C6000_EHTYPE:
    case BFD_RELOC_C6000_PREL31:
    case BFD_RELOC_C6000_PCR_H16:
    case BFD_RELOC_C6000_PCR_L16:
      return false;

    default:
      return true;
    }
}

/* Given the fine-grained form of an operand, return the coarse
   (bit-mask) form.  */

static unsigned int
tic6x_coarse_operand_form (tic6x_operand_form form)
{
  switch (form)
    {
    case tic6x_operand_asm_const:
    case tic6x_operand_link_const:
      return TIC6X_OP_EXP;

    case tic6x_operand_reg:
    case tic6x_operand_xreg:
    case tic6x_operand_dreg:
    case tic6x_operand_areg:
    case tic6x_operand_retreg:
      return TIC6X_OP_REG;

    case tic6x_operand_regpair:
    case tic6x_operand_xregpair:
    case tic6x_operand_dregpair:
      return TIC6X_OP_REGPAIR;

    case tic6x_operand_irp:
      return TIC6X_OP_IRP;

    case tic6x_operand_nrp:
      return TIC6X_OP_NRP;

    case tic6x_operand_ctrl:
      return TIC6X_OP_CTRL;

    case tic6x_operand_mem_short:
    case tic6x_operand_mem_long:
    case tic6x_operand_mem_deref:
      return TIC6X_OP_MEM_NOUNREG;

    case tic6x_operand_mem_ndw:
      return TIC6X_OP_MEM_UNREG;

    case tic6x_operand_func_unit:
      return TIC6X_OP_FUNC_UNIT;

    default:
      /* An unhandled enum value indicates a programming error or an invalid input.
       * Replacing abort() with a sentinel return value improves maintainability and reliability
       * by allowing the caller to handle the error gracefully, instead of
       * terminating the program abruptly. ~0U is a common way to signal an error
       * for an unsigned integer return type. */
      return ~0U;
    }
}

/* How an operand may match or not match a desired form.  If different
   instruction alternatives fail in different ways, the first failure
   in this list determines the diagnostic.  */
typedef enum
  {
    /* Matches.  */
    tic6x_match_matches,
    /* Bad coarse form.  */
    tic6x_match_coarse,
    /* Not constant.  */
    tic6x_match_non_const,
    /* Register on wrong side.  */
    tic6x_match_wrong_side,
    /* Not a valid address register.  */
    tic6x_match_bad_address,
    /* Not a valid return address register.  */
    tic6x_match_bad_return,
    /* Control register not readable.  */
    tic6x_match_ctrl_write_only,
    /* Control register not writable.  */
    tic6x_match_ctrl_read_only,
    /* Not a valid memory reference for this instruction.  */
    tic6x_match_bad_mem
  } tic6x_operand_match;

/* Return whether an operand matches the given fine-grained form and
   read/write usage, and, if it does not match, how it fails to match.
   The main functional unit side is SIDE; the cross-path side is CROSS
   (the same as SIDE if a cross path not used); the data side is
   DATA_SIDE.  */
static tic6x_operand_match
tic6x_operand_matches_form (const tic6x_operand *op, tic6x_operand_form form,
			    tic6x_rw rw, unsigned int side, unsigned int cross,
			    unsigned int data_side)
{
  unsigned int coarse = tic6x_coarse_operand_form (form);

  if (coarse != op->form)
    return tic6x_match_coarse;

  switch (form)
    {
    case tic6x_operand_asm_const:
      return (op->value.exp.X_op == O_constant)
             ? tic6x_match_matches
             : tic6x_match_non_const;

    case tic6x_operand_link_const:
    case tic6x_operand_irp:
    case tic6x_operand_nrp:
    case tic6x_operand_func_unit:
      return tic6x_match_matches;

    case tic6x_operand_reg:
    case tic6x_operand_regpair:
      return (op->value.reg.side == side)
             ? tic6x_match_matches
             : tic6x_match_wrong_side;

    case tic6x_operand_xreg:
    case tic6x_operand_xregpair:
      return (op->value.reg.side == cross)
             ? tic6x_match_matches
             : tic6x_match_wrong_side;

    case tic6x_operand_dreg:
    case tic6x_operand_dregpair:
      return (op->value.reg.side == data_side)
             ? tic6x_match_matches
             : tic6x_match_wrong_side;

    case tic6x_operand_areg:
      if (op->value.reg.side != cross)
        return tic6x_match_wrong_side;
      return (cross == 2 && (op->value.reg.num == 14 || op->value.reg.num == 15))
             ? tic6x_match_matches
             : tic6x_match_bad_address;

    case tic6x_operand_retreg:
      if (op->value.reg.side != side)
        return tic6x_match_wrong_side;
      return (op->value.reg.num == 3)
             ? tic6x_match_matches
             : tic6x_match_bad_return;

    case tic6x_operand_ctrl:
      {
        tic6x_rw ctrl_access = tic6x_ctrl_table[op->value.ctrl].rw;
        switch (rw)
          {
          case tic6x_rw_read:
            return (ctrl_access == tic6x_rw_read || ctrl_access == tic6x_rw_read_write)
                   ? tic6x_match_matches
                   : tic6x_match_ctrl_write_only;

          case tic6x_rw_write:
            return (ctrl_access == tic6x_rw_write || ctrl_access == tic6x_rw_read_write)
                   ? tic6x_match_matches
                   : tic6x_match_ctrl_read_only;

          default:
            abort ();
          }
      }

    case tic6x_operand_mem_deref:
      if (op->value.mem.mod != tic6x_mem_mod_none)
        return tic6x_match_bad_mem;
      if (op->value.mem.scaled != tic6x_offset_none)
        abort ();
      return (op->value.mem.base_reg.side == side)
             ? tic6x_match_matches
             : tic6x_match_bad_mem;

    case tic6x_operand_mem_short:
    case tic6x_operand_mem_ndw:
      if (op->value.mem.base_reg.side != side)
        return tic6x_match_bad_mem;

      if (op->value.mem.mod == tic6x_mem_mod_none)
        {
          if (op->value.mem.scaled != tic6x_offset_none)
            abort ();
          return tic6x_match_matches;
        }

      if (op->value.mem.scaled == tic6x_offset_none)
        {
          if (op->value.mem.mod == tic6x_mem_mod_plus
              || op->value.mem.mod == tic6x_mem_mod_minus)
            abort ();
          return tic6x_match_matches;
        }

      if (op->value.mem.offset_is_reg)
        {
          if (op->value.mem.scaled == tic6x_offset_unscaled
              && form != tic6x_operand_mem_ndw)
            abort ();
          return (op->value.mem.offset.reg.side == side)
                 ? tic6x_match_matches
                 : tic6x_match_bad_mem;
        }
      else
        {
          return (op->value.mem.offset.exp.X_op == O_constant)
                 ? tic6x_match_matches
                 : tic6x_match_bad_mem;
        }

    case tic6x_operand_mem_long:
      if (!(op->value.mem.base_reg.side == 2
            && (op->value.mem.base_reg.num == 14
                || op->value.mem.base_reg.num == 15)))
        return tic6x_match_bad_mem;

      switch (op->value.mem.mod)
        {
        case tic6x_mem_mod_none:
          if (op->value.mem.scaled != tic6x_offset_none)
            abort ();
          return tic6x_match_matches;

        case tic6x_mem_mod_plus:
          if (op->value.mem.scaled == tic6x_offset_none)
            abort ();
          if (op->value.mem.offset_is_reg)
            return tic6x_match_bad_mem;
          if (op->value.mem.scaled == tic6x_offset_scaled
              && op->value.mem.offset.exp.X_op != O_constant)
            return tic6x_match_bad_mem;
          return tic6x_match_matches;

        case tic6x_mem_mod_minus:
        case tic6x_mem_mod_preinc:
        case tic6x_mem_mod_predec:
        case tic6x_mem_mod_postinc:
        case tic6x_mem_mod_postdec:
          return tic6x_match_bad_mem;

        default:
          abort ();
        }

    default:
      abort ();
    }
}

/* Return the number of bits shift used with DP-relative coding method
   CODING.  */

static unsigned int
tic6x_dpr_shift (tic6x_coding_method coding)
{
  switch (coding)
    {
    case tic6x_coding_ulcst_dpr_byte:
      return 0;

    case tic6x_coding_ulcst_dpr_half:
      return 1;

    case tic6x_coding_ulcst_dpr_word:
      return 2;

    default:
      exit (EXIT_FAILURE);
    }
}

/* Return the relocation used with DP-relative coding method
   CODING.  */

static bfd_reloc_code_real_type
tic6x_dpr_reloc (tic6x_coding_method coding)
{
  switch (coding)
    {
    case tic6x_coding_ulcst_dpr_byte:
      return BFD_RELOC_C6000_SBR_U15_B;

    case tic6x_coding_ulcst_dpr_half:
      return BFD_RELOC_C6000_SBR_U15_H;

    case tic6x_coding_ulcst_dpr_word:
      return BFD_RELOC_C6000_SBR_U15_W;

    default:
      assert(0 && "Unhandled tic6x_coding_method value encountered");
      abort ();
    }
}

/* Given a memory reference *MEM_REF as originally parsed, fill in
   defaults for missing offsets.  */

static void
init_constant_offset_expression(tic6x_mem_ref *mem_ref, int value)
{
  mem_ref->offset_is_reg = false;
  memset(&mem_ref->offset.exp, 0, sizeof mem_ref->offset.exp);
  mem_ref->offset.exp.X_op = O_constant;
  mem_ref->offset.exp.X_add_number = value;
  mem_ref->offset.exp.X_unsigned = 0;
}

static void
tic6x_default_mem_ref (tic6x_mem_ref *mem_ref)
{
  switch (mem_ref->mod)
    {
    case tic6x_mem_mod_none:
      if (mem_ref->scaled != tic6x_offset_none)
        abort();
      mem_ref->mod = tic6x_mem_mod_plus;
      mem_ref->scaled = tic6x_offset_unscaled;
      init_constant_offset_expression(mem_ref, 0);
      break;

    case tic6x_mem_mod_plus:
    case tic6x_mem_mod_minus:
      if (mem_ref->scaled == tic6x_offset_none)
        abort();
      break;

    case tic6x_mem_mod_preinc:
    case tic6x_mem_mod_predec:
    case tic6x_mem_mod_postinc:
    case tic6x_mem_mod_postdec:
      if (mem_ref->scaled == tic6x_offset_none)
        {
          mem_ref->scaled = tic6x_offset_scaled;
          init_constant_offset_expression(mem_ref, 1);
        }
      break;

    default:
      abort();
    }
}

/* Return the encoding in the 8-bit field of an SPMASK or SPMASKR
   instruction of the specified UNIT, side SIDE.  */

#include <stdlib.h>
#include <limits.h>

static unsigned int
tic6x_encode_spmask (tic6x_func_unit_base unit, unsigned int side)
{
  unsigned int shift_amount;
  const unsigned int max_shift_bits = sizeof(unsigned int) * CHAR_BIT;

  switch (unit)
    {
    case tic6x_func_unit_l:
      shift_amount = side - 1;
      break;

    case tic6x_func_unit_s:
      shift_amount = side + 1;
      break;

    case tic6x_func_unit_d:
      shift_amount = side + 3;
      break;

    case tic6x_func_unit_m:
      shift_amount = side + 5;
      break;

    default:
      abort ();
    }

  if (shift_amount >= max_shift_bits)
    {
      abort();
    }

  return 1U << shift_amount;
}

/* Try to encode the instruction with opcode number ID and operands
   OPERANDS (number NUM_OPERANDS), creg value THIS_LINE_CREG and z
   value THIS_LINE_Z; FUNC_UNIT_SIDE, FUNC_UNIT_CROSS and
   FUNC_UNIT_DATA_SIDE describe the functional unit specification;
   SPLOOP_II is the ii value from the previous SPLOOP-family
   instruction, or 0 if not in such a loop; the only possible problems
   are operands being out of range (they already match the
   fine-grained form), and inappropriate predication.  If this
   succeeds, return the encoding and set *OK to true; otherwise return
   0 and set *OK to FALSE.  If a fix is needed, set *FIX_NEEDED to
   true and fill in *FIX_EXP, *FIX_PCREL, *FX_R_TYPE and *FIX_ADDA.
   Print error messages for failure if PRINT_ERRORS is true; the
   opcode starts at STR and has length OPC_LEN.  */

#include "as.h"
#include "bfd.h"
#include "opcode/tic6x.h"
#include <stdbool.h>

/* Forward declarations for helper functions. */
static bool report_operand_error(bool print_errors, const char *format, unsigned int opno,
                                 int opc_len, const char *str, bool *ok, ...);
static bool report_instruction_error(bool print_errors, const char *format,
                                     int opc_len, const char *str, bool *ok);
static bool report_internal_encoding_error(bool print_errors, const char *details,
                                           int opc_len, const char *str, bool *ok);

static bool encode_unsigned_constant_value(const tic6x_operand *operand,
                                           const tic6x_insn_field *fldd,
                                           bool print_errors, unsigned int opno,
                                           int opc_len, const char *str,
                                           bool *ok, unsigned int *out_value);
static bool encode_signed_constant_value(const tic6x_operand *operand,
                                         const tic6x_insn_field *fldd,
                                         bool print_errors, unsigned int opno,
                                         int opc_len, const char *str,
                                         bool *ok, unsigned int *out_value,
                                         bool negate);
static bool handle_ulcst_dpr_coding_method(const tic6x_operand *operand,
                                           const tic6x_opcode_variable_field *var_fld,
                                           const tic6x_insn_field *fldd,
                                           bool print_errors, unsigned int opno,
                                           int opc_len, const char *str,
                                           bool *fix_needed, expressionS **fix_exp,
                                           int *fix_pcrel, bfd_reloc_code_real_type *fx_r_type,
                                           bool *fix_adda, bool *ok, unsigned int *out_value);
static bool handle_sploop_coding_method(const tic6x_operand *operand,
                                        const tic6x_opcode_variable_field *var_fld,
                                        const tic6x_insn_field *fldd,
                                        bool print_errors, unsigned int opno,
                                        int opc_len, const char *str,
                                        int sploop_ii, bool *ok,
                                        unsigned int *out_value);


/* Helper for common operand-specific error reporting pattern. */
static bool
report_operand_error (bool print_errors, const char *format, unsigned int opno,
                      int opc_len, const char *str, bool *ok, ...)
{
  if (print_errors)
    {
      va_list args;
      va_start (args, ok);
      as_bad_flv (NULL, 0, _(format), opno + 1, opc_len, str, args);
      va_end (args);
    }
  *ok = false;
  return true; /* Indicates an error occurred. */
}

/* Helper for instruction-specific error reporting. */
static bool
report_instruction_error (bool print_errors, const char *format,
                          int opc_len, const char *str, bool *ok)
{
  if (print_errors)
    as_bad (_(format), opc_len, str);
  *ok = false;
  return true; /* Indicates an error occurred. */
}

/* Helper for internal consistency errors (replacing aborts). */
static bool
report_internal_encoding_error (bool print_errors, const char *details,
                                int opc_len, const char *str, bool *ok)
{
  if (print_errors)
    as_bad (_("internal encoding error for '%.*s': %s"), opc_len, str, details);
  *ok = false;
  return true; /* Indicates an error occurred. */
}

/* Helper for unsigned constant encoding. */
static bool
encode_unsigned_constant_value (const tic6x_operand *operand,
                                const tic6x_insn_field *fldd,
                                bool print_errors, unsigned int opno,
                                int opc_len, const char *str,
                                bool *ok, unsigned int *out_value)
{
  if (operand->form != TIC6X_OP_EXP || operand->value.exp.X_op != O_constant)
    return report_internal_encoding_error(print_errors, "expected constant expression for unsigned constant field", opc_len, str, ok);

  long long constant_value = operand->value.exp.X_add_number;
  unsigned int max_val_exclusive = (1U << fldd->bitfields[0].width);

  if (constant_value < 0 || constant_value >= max_val_exclusive)
    return report_operand_error(print_errors, "operand %u of '%.*s' out of range", opno, opc_len, str, ok);

  *out_value = (unsigned int)constant_value;
  return false; /* No error. */
}

/* Helper for signed constant encoding. */
static bool
encode_signed_constant_value (const tic6x_operand *operand,
                              const tic6x_insn_field *fldd,
                              bool print_errors, unsigned int opno,
                              int opc_len, const char *str,
                              bool *ok, unsigned int *out_value,
                              bool negate)
{
  if (operand->form != TIC6X_OP_EXP || operand->value.exp.X_op != O_constant)
    return report_internal_encoding_error(print_errors, "expected constant expression for signed constant field", opc_len, str, ok);

  offsetT sign_value = operand->value.exp.X_add_number;
  if (negate)
    sign_value = -sign_value;

  /* Assuming SEXT is a macro/function defined elsewhere that performs sign extension. */
  sign_value = SEXT(sign_value);

  long long min_val = -(1LL << (fldd->bitfields[0].width - 1));
  long long max_val = (1LL << (fldd->bitfields[0].width - 1)); /* Exclusive upper bound. */

  if (sign_value < min_val || sign_value >= max_val)
    return report_operand_error(print_errors, "operand %u of '%.*s' out of range", opno, opc_len, str, ok);

  /* Convert to unsigned representation with MSB inverted, as per original logic. */
  *out_value = (unsigned int)(sign_value + max_val);
  *out_value ^= (1U << (fldd->bitfields[0].width - 1));

  return false; /* No error. */
}

/* Helper for ulcst_dpr encoding logic. */
static bool
handle_ulcst_dpr_coding_method (const tic6x_operand *operand,
                                const tic6x_opcode_variable_field *var_fld,
                                const tic6x_insn_field *fldd,
                                bool print_errors, unsigned int opno,
                                int opc_len, const char *str,
                                bool *fix_needed, expressionS **fix_exp,
                                int *fix_pcrel, bfd_reloc_code_real_type *fx_r_type,
                                bool *fix_adda, bool *ok, unsigned int *out_value)
{
  unsigned int bits = tic6x_dpr_shift (var_fld->coding_method);
  expressionS *expp = NULL;
  unsigned int value_to_encode = 0;

  switch (operand->form)
    {
    case TIC6X_OP_EXP:
      if (operand->value.exp.X_op == O_constant)
        {
          long long constant_value = operand->value.exp.X_add_number;
          unsigned int max_val_exclusive = (1U << fldd->bitfields[0].width);
          if (constant_value < 0 || constant_value >= max_val_exclusive)
            return report_operand_error(print_errors, "operand %u of '%.*s' out of range", opno, opc_len, str, ok);
          value_to_encode = (unsigned int)constant_value;
        }
      else
        {
          expp = &operand->value.exp;
        }
      break;

    case TIC6X_OP_MEM_NOUNREG:
      {
        tic6x_mem_ref mem = operand->value.mem;
        tic6x_default_mem_ref (&mem);

        if (mem.offset_is_reg)
          return report_internal_encoding_error(print_errors, "memory offset cannot be register for ulcst_dpr", opc_len, str, ok);

        if (mem.offset.exp.X_op == O_constant)
          {
            long long constant_value = mem.offset.exp.X_add_number;
            unsigned int max_val_exclusive = (1U << fldd->bitfields[0].width);

            if (mem.scaled == tic6x_offset_unscaled)
              {
                if (constant_value & ((1U << bits) - 1))
                  {
                    if (print_errors)
                      as_bad (_("offset in operand %u of '%.*s' not "
                                "divisible by %u"), opno + 1, opc_len,
                              str, 1U << bits);
                    *ok = false;
                    return true;
                  }
                constant_value >>= bits;
              }
            if (constant_value < 0 || constant_value >= max_val_exclusive)
              return report_operand_error(print_errors, "offset in operand %u of '%.*s' out of range", opno, opc_len, str, ok);
            value_to_encode = (unsigned int)constant_value;
          }
        else
          {
            if (mem.scaled != tic6x_offset_unscaled
                || operand->value.mem.mod != tic6x_mem_mod_none
                || operand->value.mem.offset_is_reg) /* Original logic's redundant check for mem.scaled and offset_is_reg. */
              return report_internal_encoding_error(print_errors, "unexpected memory operand format for ulcst_dpr with non-constant offset", opc_len, str, ok);
            expp = &operand->value.mem.offset.exp;
          }
      }
      break;

    default:
      return report_internal_encoding_error(print_errors, "unexpected operand form for ulcst_dpr encoding", opc_len, str, ok);
    }

  if (expp != NULL) /* Relocation needed. */
    {
      if (fldd->bitfields[0].low_pos != 8 || fldd->bitfields[0].width != 15)
        return report_internal_encoding_error(print_errors, "unexpected field definition for ulcst_dpr relocation", opc_len, str, ok);

      *fix_needed = true;
      *fix_exp = expp;
      *fix_pcrel = 0;
      *fx_r_type = tic6x_dpr_reloc (var_fld->coding_method);
      *fix_adda = (operand->form == TIC6X_OP_EXP);
      *out_value = 0; /* Value for relocation will be filled by linker. */
    }
  else
    {
      *out_value = value_to_encode;
    }
  return false; /* No error. */
}

/* Helper for fstg/fcyc coding logic. */
static bool
handle_sploop_coding_method (const tic6x_operand *operand,
                             const tic6x_opcode_variable_field *var_fld,
                             const tic6x_insn_field *fldd,
                             bool print_errors, unsigned int opno,
                             int opc_len, const char *str,
                             int sploop_ii, bool *ok,
                             unsigned int *out_value)
{
  if (operand->form != TIC6X_OP_EXP || operand->value.exp.X_op != O_constant)
    return report_internal_encoding_error(print_errors, "expected constant expression for software pipelined loop field", opc_len, str, ok);

  if (!sploop_ii)
    return report_instruction_error(print_errors, "'%.*s' instruction not in a software pipelined loop", opc_len, str, ok);

  unsigned int fcyc_bits;
  if (sploop_ii <= 1) fcyc_bits = 0;
  else if (sploop_ii <= 2) fcyc_bits = 1;
  else if (sploop_ii <= 4) fcyc_bits = 2;
  else if (sploop_ii <= 8) fcyc_bits = 3;
  else if (sploop_ii <= 14) fcyc_bits = 4;
  else
    return report_internal_encoding_error(print_errors, "unsupported sploop_ii value", opc_len, str, ok);

  if (fcyc_bits > fldd->bitfields[0].width)
    return report_internal_encoding_error(print_errors, "fcyc_bits exceeds field width for software pipelined loop field", opc_len, str, ok);

  long long constant_value = operand->value.exp.X_add_number;

  if (var_fld->coding_method == tic6x_coding_fstg)
    {
      unsigned int max_stg_value_exclusive = (1U << (fldd->bitfields[0].width - fcyc_bits));
      if (constant_value < 0 || constant_value >= max_stg_value_exclusive)
        return report_operand_error(print_errors, "operand %u of '%.*s' out of range", opno, opc_len, str, ok);

      unsigned int temp_value = (unsigned int)constant_value;
      unsigned int t = 0;
      for (int i = fcyc_bits; i < (int)fldd->bitfields[0].width; i++)
        {
          t = (t << 1) | (temp_value & 1);
          temp_value >>= 1;
        }
      *out_value = t << fcyc_bits;
    }
  else /* tic6x_coding_fcyc */
    {
      if (constant_value < 0 || constant_value >= sploop_ii)
        return report_operand_error(print_errors, "operand %u of '%.*s' out of range", opno, opc_len, str, ok);
      *out_value = (unsigned int)constant_value;
    }
  return false; /* No error. */
}


static unsigned int
tic6x_try_encode (tic6x_opcode_id id, tic6x_operand *operands,
		  unsigned int num_operands, unsigned int this_line_creg,
		  unsigned int this_line_z, unsigned int func_unit_side,
		  unsigned int func_unit_cross,
		  unsigned int func_unit_data_side, int sploop_ii,
		  expressionS **fix_exp, int *fix_pcrel,
		  bfd_reloc_code_real_type *fx_r_type, bool *fix_adda,
		  bool *fix_needed, bool *ok,
		  bool print_errors, char *str, int opc_len)
{
  const tic6x_opcode *opct;
  const tic6x_insn_format *fmt;
  unsigned int opcode_value;

  *ok = false; /* Assume failure until success path completes. */
  *fix_needed = false;

  opct = &tic6x_opcode_table[id];
  fmt = &tic6x_insn_format_table[opct->format];
  opcode_value = fmt->cst_bits;

  /* Process fixed fields. */
  for (unsigned int fld_idx = 0; fld_idx < opct->num_fixed_fields; fld_idx++)
    {
      if (opct->fixed_fields[fld_idx].min_val == opct->fixed_fields[fld_idx].max_val)
	{
	  const tic6x_insn_field *fldd = tic6x_field_from_fmt (fmt, opct->fixed_fields[fld_idx].field_id);
	  if (fldd == NULL)
	    return report_internal_encoding_error(print_errors, "missing field definition for fixed field", opc_len, str, ok) ? 0 : 0;
	  opcode_value |= opct->fixed_fields[fld_idx].min_val << fldd->bitfields[0].low_pos;
	}
    }

  /* Process variable fields. */
  for (unsigned int fld_idx = 0; fld_idx < opct->num_variable_fields; fld_idx++)
    {
      const tic6x_insn_field *fldd = tic6x_field_from_fmt (fmt, opct->variable_fields[fld_idx].field_id);
      if (fldd == NULL)
	return report_internal_encoding_error(print_errors, "missing field definition for variable field", opc_len, str, ok) ? 0 : 0;

      unsigned int opno = opct->variable_fields[fld_idx].operand_num;
      unsigned int value = 0; /* Value to encode into opcode_value. */

      if (opno >= num_operands)
        return report_internal_encoding_error(print_errors, "variable field refers to non-existent operand", opc_len, str, ok) ? 0 : 0;
      
      const tic6x_operand *current_operand = &operands[opno];
      const tic6x_opcode_variable_field *var_fld = &opct->variable_fields[fld_idx];

      switch (var_fld->coding_method)
	{
	case tic6x_coding_ucst:
	  if (encode_unsigned_constant_value(current_operand, fldd, print_errors, opno, opc_len, str, ok, &value)) return 0;
	  break;

	case tic6x_coding_scst:
	  if (current_operand->form != TIC6X_OP_EXP || current_operand->value.exp.X_op != O_constant)
	    {
	      if (fldd->bitfields[0].low_pos != 7 || fldd->bitfields[0].width != 16)
		return report_internal_encoding_error(print_errors, "unsupported field definition for symbolic signed constant", opc_len, str, ok) ? 0 : 0;
	      *fix_needed = true;
	      *fix_exp = &current_operand->value.exp;
	      *fix_pcrel = 0;
	      *fx_r_type = BFD_RELOC_C6000_ABS_S16;
	      *fix_adda = false;
	      value = 0; /* Relocations encode 0 initially. */
	    }
	  else
	    {
	      if (encode_signed_constant_value(current_operand, fldd, print_errors, opno, opc_len, str, ok, &value, false)) return 0;
	    }
	  break;

	case tic6x_coding_ucst_minus_one:
	  if (current_operand->form != TIC6X_OP_EXP || current_operand->value.exp.X_op != O_constant)
	    return report_internal_encoding_error(print_errors, "expected constant expression for ucst_minus_one field", opc_len, str, ok) ? 0 : 0;
	  {
	    long long constant_value = current_operand->value.exp.X_add_number;
	    unsigned int max_val_plus_one = (1U << fldd->bitfields[0].width);
	    if (constant_value <= 0 || constant_value > max_val_plus_one)
	      return report_operand_error(print_errors, "operand %u of '%.*s' out of range", opno, opc_len, str, ok);
	    value = (unsigned int)constant_value - 1;
	  }
	  break;

	case tic6x_coding_scst_negate:
	  if (encode_signed_constant_value(current_operand, fldd, print_errors, opno, opc_len, str, ok, &value, true)) return 0;
	  break;

	case tic6x_coding_ulcst_dpr_byte:
	case tic6x_coding_ulcst_dpr_half:
	case tic6x_coding_ulcst_dpr_word:
	  if (handle_ulcst_dpr_coding_method(current_operand, var_fld, fldd, print_errors, opno, opc_len, str,
	                                     fix_needed, fix_exp, fix_pcrel, fx_r_type, fix_adda, ok, &value)) return 0;
	  break;

	case tic6x_coding_lcst_low16:
	  if (current_operand->form != TIC6X_OP_EXP)
	    return report_internal_encoding_error(print_errors, "expected expression for lcst_low16", opc_len, str, ok) ? 0 : 0;
	  if (current_operand->value.exp.X_op == O_constant)
	    value = current_operand->value.exp.X_add_number & 0xffff;
	  else
	    {
	      if (fldd->bitfields[0].low_pos != 7 || fldd->bitfields[0].width != 16)
		return report_internal_encoding_error(print_errors, "unsupported field definition for symbolic lcst_low16", opc_len, str, ok) ? 0 : 0;
	      *fix_needed = true;
	      *fix_exp = &current_operand->value.exp;
	      *fix_pcrel = 0;
	      *fx_r_type = BFD_RELOC_C6000_ABS_L16;
	      *fix_adda = false;
	      value = 0;
	    }
	  break;

	case tic6x_coding_lcst_high16:
	  if (current_operand->form != TIC6X_OP_EXP)
	    return report_internal_encoding_error(print_errors, "expected expression for lcst_high16", opc_len, str, ok) ? 0 : 0;
	  if (current_operand->value.exp.X_op == O_constant)
	    value = (current_operand->value.exp.X_add_number >> 16) & 0xffff;
	  else
	    {
	      if (fldd->bitfields[0].low_pos != 7 || fldd->bitfields[0].width != 16)
		return report_internal_encoding_error(print_errors, "unsupported field definition for symbolic lcst_high16", opc_len, str, ok) ? 0 : 0;
	      *fix_needed = true;
	      *fix_exp = &current_operand->value.exp;
	      *fix_pcrel = 0;
	      *fx_r_type = BFD_RELOC_C6000_ABS_H16;
	      *fix_adda = false;
	      value = 0;
	    }
	  break;

	case tic6x_coding_pcrel:
	case tic6x_coding_pcrel_half:
	  if (current_operand->form != TIC6X_OP_EXP)
	    return report_internal_encoding_error(print_errors, "expected expression for pcrel", opc_len, str, ok) ? 0 : 0;
	  value = 0;
	  *fix_needed = true;
	  *fix_exp = &current_operand->value.exp;
	  *fix_pcrel = 1;
	  if (fldd->bitfields[0].low_pos == 7 && fldd->bitfields[0].width == 21)
	    *fx_r_type = BFD_RELOC_C6000_PCR_S21;
	  else if (fldd->bitfields[0].low_pos == 16 && fldd->bitfields[0].width == 12)
	    *fx_r_type = BFD_RELOC_C6000_PCR_S12;
	  else if (fldd->bitfields[0].low_pos == 13 && fldd->bitfields[0].width == 10)
	    *fx_r_type = BFD_RELOC_C6000_PCR_S10;
	  else if (fldd->bitfields[0].low_pos == 16 && fldd->bitfields[0].width == 7)
	    *fx_r_type = BFD_RELOC_C6000_PCR_S7;
	  else
	    return report_internal_encoding_error(print_errors, "unsupported field definition for pcrel relocation", opc_len, str, ok) ? 0 : 0;
	  *fix_adda = false;
	  break;

	case tic6x_coding_regpair_lsb:
	  if (current_operand->form != TIC6X_OP_REGPAIR)
	    return report_internal_encoding_error(print_errors, "expected register pair for regpair_lsb", opc_len, str, ok) ? 0 : 0;
	  value = current_operand->value.reg.num;
	  break;

	case tic6x_coding_regpair_msb:
	  if (current_operand->form != TIC6X_OP_REGPAIR)
	    return report_internal_encoding_error(print_errors, "expected register pair for regpair_msb", opc_len, str, ok) ? 0 : 0;
	  value = current_operand->value.reg.num + 1;
	  break;

	case tic6x_coding_reg:
	  switch (current_operand->form)
	    {
	    case TIC6X_OP_REG:
	    case TIC6X_OP_REGPAIR:
	      value = current_operand->value.reg.num;
	      break;
	    case TIC6X_OP_MEM_NOUNREG:
	    case TIC6X_OP_MEM_UNREG:
	      value = current_operand->value.mem.base_reg.num;
	      break;
	    default:
	      return report_internal_encoding_error(print_errors, "unexpected operand form for register field", opc_len, str, ok) ? 0 : 0;
	    }
	  break;

	case tic6x_coding_areg:
	  switch (current_operand->form)
	    {
	    case TIC6X_OP_REG:
	      value = (current_operand->value.reg.num == 15 ? 1 : 0);
	      break;
	    case TIC6X_OP_MEM_NOUNREG:
	      value = (current_operand->value.mem.base_reg.num == 15 ? 1 : 0);
	      break;
	    default:
	      return report_internal_encoding_error(print_errors, "unexpected operand form for areg field", opc_len, str, ok) ? 0 : 0;
	    }
	  break;

	case tic6x_coding_crlo:
	  if (current_operand->form != TIC6X_OP_CTRL)
	    return report_internal_encoding_error(print_errors, "expected control register for crlo field", opc_len, str, ok) ? 0 : 0;
	  value = tic6x_ctrl_table[current_operand->value.ctrl].crlo;
	  break;

	case tic6x_coding_crhi:
	  if (current_operand->form != TIC6X_OP_CTRL)
	    return report_internal_encoding_error(print_errors, "expected control register for crhi field", opc_len, str, ok) ? 0 : 0;
	  value = 0; /* Value always 0 as per original. */
	  break;

	case tic6x_coding_reg_shift:
	  if (current_operand->form != TIC6X_OP_REGPAIR)
	    return report_internal_encoding_error(print_errors, "expected register pair for reg_shift field", opc_len, str, ok) ? 0 : 0;
	  value = current_operand->value.reg.num >> 1;
	  break;

	case tic6x_coding_mem_offset:
	  if (current_operand->form != TIC6X_OP_MEM_NOUNREG)
	    return report_internal_encoding_error(print_errors, "expected memory operand for mem_offset field", opc_len, str, ok) ? 0 : 0;
	  {
	    tic6x_mem_ref mem = current_operand->value.mem;
	    tic6x_default_mem_ref (&mem); /* Modifies mem in place. */

	    if (mem.offset_is_reg)
	      {
		if (mem.scaled != tic6x_offset_scaled)
		  return report_internal_encoding_error(print_errors, "expected scaled memory for register offset", opc_len, str, ok) ? 0 : 0;
		value = mem.offset.reg.num;
	      }
	    else
	      {
		int scale;
		if (mem.offset.exp.X_op != O_constant)
		  return report_internal_encoding_error(print_errors, "expected constant offset for memory operand", opc_len, str, ok) ? 0 : 0;

		switch (mem.scaled)
		  {
		  case tic6x_offset_scaled:
		    scale = 1;
		    break;
		  case tic6x_offset_unscaled:
		    scale = opct->operand_info[opno].size;
		    if (scale != 1 && scale != 2 && scale != 4 && scale != 8)
		      return report_internal_encoding_error(print_errors, "unsupported unscaled memory operand size", opc_len, str, ok) ? 0 : 0;
		    break;
		  default:
		    return report_internal_encoding_error(print_errors, "unknown memory scaling type", opc_len, str, ok) ? 0 : 0;
		  }

		long long constant_value = mem.offset.exp.X_add_number;
		unsigned int max_range_exclusive = (1U << fldd->bitfields[0].width) * scale;
		if (constant_value < 0 || constant_value >= max_range_exclusive)
		  return report_operand_error(print_errors, "offset in operand %u of '%.*s' out of range", opno, opc_len, str, ok);

		if (constant_value % scale)
		  return report_operand_error(print_errors, "offset in operand %u of '%.*s' not divisible by %u", opno, opc_len, str, ok, scale);

		value = (unsigned int)(constant_value / scale);
	      }
	  }
	  break;

	case tic6x_coding_mem_offset_noscale:
	  if (current_operand->form != TIC6X_OP_MEM_UNREG)
	    return report_internal_encoding_error(print_errors, "expected unregister memory operand for mem_offset_noscale", opc_len, str, ok) ? 0 : 0;
	  {
	    tic6x_mem_ref mem = current_operand->value.mem;
	    tic6x_default_mem_ref (&mem);

	    if (mem.offset_is_reg)
	      value = mem.offset.reg.num;
	    else
	      {
		if (mem.offset.exp.X_op != O_constant)
		  return report_internal_encoding_error(print_errors, "expected constant offset for mem_offset_noscale", opc_len, str, ok) ? 0 : 0;
		long long constant_value = mem.offset.exp.X_add_number;
		unsigned int max_val_exclusive = (1U << fldd->bitfields[0].width);
		if (constant_value < 0 || constant_value >= max_val_exclusive)
		  return report_operand_error(print_errors, "offset in operand %u of '%.*s' out of range", opno, opc_len, str, ok);
		value = (unsigned int)constant_value;
	      }
	  }
	  break;

	case tic6x_coding_mem_mode:
	  if (current_operand->form != TIC6X_OP_MEM_NOUNREG && current_operand->form != TIC6X_OP_MEM_UNREG)
	    return report_internal_encoding_error(print_errors, "expected memory operand for mem_mode field", opc_len, str, ok) ? 0 : 0;
	  {
	    tic6x_mem_ref mem = current_operand->value.mem;
	    tic6x_default_mem_ref (&mem);
	    switch (mem.mod)
	      {
	      case tic6x_mem_mod_plus: value = 1; break;
	      case tic6x_mem_mod_minus: value = 0; break;
	      case tic6x_mem_mod_preinc: value = 9; break;
	      case tic6x_mem_mod_predec: value = 8; break;
	      case tic6x_mem_mod_postinc: value = 11; break;
	      case tic6x_mem_mod_postdec: value = 10; break;
	      default:
		return report_internal_encoding_error(print_errors, "unknown memory modification mode", opc_len, str, ok) ? 0 : 0;
	      }
	    value += (mem.offset_is_reg ? 4 : 0);
	  }
	  break;

	case tic6x_coding_scaled:
	  if (current_operand->form != TIC6X_OP_MEM_UNREG)
	    return report_internal_encoding_error(print_errors, "expected unregister memory operand for scaled field", opc_len, str, ok) ? 0 : 0;
	  {
	    tic6x_mem_ref mem = current_operand->value.mem;
	    tic6x_default_mem_ref (&mem);
	    switch (mem.scaled)
	      {
	      case tic6x_offset_unscaled: value = 0; break;
	      case tic6x_offset_scaled: value = 1; break;
	      default:
		return report_internal_encoding_error(print_errors, "unknown memory scaling type for scaled field", opc_len, str, ok) ? 0 : 0;
	      }
	  }
	  break;

	case tic6x_coding_spmask:
	  if (fldd->bitfields[0].low_pos != 18)
	    return report_internal_encoding_error(print_errors, "spmask field not at expected position", opc_len, str, ok) ? 0 : 0;
	  value = 0;
	  for (unsigned int mask_op_idx = 0; mask_op_idx < num_operands; mask_op_idx++)
	    {
	      unsigned int v;
	      /* Assuming operands for spmask are always functional units. */
	      v = tic6x_encode_spmask (operands[mask_op_idx].value.func_unit.base,
				       operands[mask_op_idx].value.func_unit.side);
	      if (value & v)
		return report_operand_error(print_errors, "functional unit already masked for operand %u of '%.*s'", mask_op_idx, opc_len, str, ok);
	      value |= v;
	    }
	  break;

	case tic6x_coding_reg_unused:
	  value = 0; /* Placeholder as per original. */
	  break;

	case tic6x_coding_fstg:
	case tic6x_coding_fcyc:
	  if (handle_sploop_coding_method(current_operand, var_fld, fldd, print_errors, opno, opc_len, str, sploop_ii, ok, &value)) return 0;
	  break;

	case tic6x_coding_fu:
	  value = func_unit_side == 2 ? 1 : 0;
	  break;

	case tic6x_coding_data_fu:
	  value = func_unit_data_side == 2 ? 1 : 0;
	  break;

	case tic6x_coding_xpath:
	  value = func_unit_cross;
	  break;

	default:
	  return report_internal_encoding_error(print_errors, "unknown coding method", opc_len, str, ok) ? 0 : 0;
	}

      /* Cross-validation with fixed fields (if any). */
      for (unsigned int ffld_idx = 0; ffld_idx < opct->num_fixed_fields; ffld_idx++)
	if ((opct->fixed_fields[ffld_idx].field_id == var_fld->field_id)
	    && (value < opct->fixed_fields[ffld_idx].min_val
		|| value > opct->fixed_fields[ffld_idx].max_val))
	  {
	    return report_operand_error(print_errors, "operand %u of '%.*s' out of range (cross-validation)", opno, opc_len, str, ok);
	  }

      opcode_value |= value << fldd->bitfields[0].low_pos;
    }

  /* Handle predication. */
  if (this_line_creg)
    {
      const tic6x_insn_field *creg_fld = tic6x_field_from_fmt (fmt, tic6x_field_creg);
      if (creg_fld == NULL)
	return report_instruction_error(print_errors, "instruction '%.*s' cannot be predicated", opc_len, str, ok) ? 0 : 0;
      
      const tic6x_insn_field *z_fld = tic6x_field_from_fmt (fmt, tic6x_field_z);
      if (z_fld == NULL) /* This implies an internal table error if creg_fld exists but z_fld doesn't. */
	return report_internal_encoding_error(print_errors, "missing 'z' field for predicated instruction", opc_len, str, ok) ? 0 : 0;

      opcode_value |= this_line_creg << creg_fld->bitfields[0].low_pos;
      opcode_value |= this_line_z << z_fld->bitfields[0].low_pos;
    }

  *ok = true;
  return opcode_value;
}

/* Convert the target integer stored in N bytes in BUF to a host
   integer, returning that value.  */

static valueT
md_chars_to_number (char *buf, int n)
{
  valueT result = 0;

  if (buf == NULL)
    {
      return 0;
    }

  if (n < 0)
    {
      return 0;
    }

  if (n > sizeof(valueT))
    {
      buf += (n - sizeof(valueT));
      n = sizeof(valueT);
    }

  if (target_big_endian)
    {
      for (int i = 0; i < n; ++i)
	{
	  result = (result << 8) | ((valueT)(unsigned char)buf[i]);
	}
    }
  else
    {
      for (int i = 0; i < n; ++i)
	{
	  result |= ((valueT)(unsigned char)buf[i]) << (i * 8);
	}
    }

  return result;
}

/* Assemble the instruction starting at STR (an opcode, with the
   opcode name all-lowercase).  */

static const char *
parse_opcode_name(const char *input_str, int *opc_len_out)
{
  const char *p = input_str;
  while (!is_end_of_stmt(*p) && !is_whitespace(*p))
    p++;

  *opc_len_out = p - input_str;

  if (*opc_len_out == 0)
    {
      as_bad(_("missing opcode"));
      return NULL;
    }
  return input_str;
}

static bool
parse_functional_unit_specifier(const char **p_ptr,
                                 tic6x_func_unit_base *func_unit_base_out,
                                 unsigned int *func_unit_side_out,
                                 unsigned int *func_unit_cross_out,
                                 unsigned int *cross_side_out,
                                 unsigned int *func_unit_data_side_out)
{
  const char *p = *p_ptr;
  if (*p != '.')
    return false;

  bool good_func_unit = false;
  tic6x_func_unit_base maybe_base = tic6x_func_unit_nfu;
  unsigned int maybe_side = 0;
  unsigned int maybe_cross = 0;
  unsigned int maybe_data_side = 0;

  good_func_unit = tic6x_parse_func_unit_base(p + 1, &maybe_base, &maybe_side);

  if (good_func_unit)
    {
      if (is_whitespace(p[3]) || is_end_of_stmt(p[3]))
        {
          p += 3;
        }
      else if ((p[3] == 'x' || p[3] == 'X')
               && (is_whitespace(p[4]) || is_end_of_stmt(p[4])))
        {
          maybe_cross = 1;
          p += 4;
        }
      else if (maybe_base == tic6x_func_unit_d
               && (p[3] == 't' || p[3] == 'T')
               && (p[4] == '1' || p[4] == '2')
               && (is_whitespace(p[5]) || is_end_of_stmt(p[5])))
        {
          maybe_data_side = p[4] - '0';
          p += 5;
        }
      else
        {
          good_func_unit = false;
        }
    }

  if (good_func_unit)
    {
      *func_unit_base_out = maybe_base;
      *func_unit_side_out = maybe_side;
      *func_unit_cross_out = maybe_cross;
      *cross_side_out = (maybe_cross ? 3 - maybe_side : maybe_side);
      *func_unit_data_side_out = maybe_data_side;
      *p_ptr = p;
      return true;
    }

  return false;
}

static bool
is_opcode_compatible(tic6x_opcode_id id,
                     tic6x_func_unit_base func_unit_base,
                     unsigned int func_unit_side,
                     unsigned int func_unit_cross,
                     unsigned int func_unit_data_side,
                     bool *overall_arch_ok_out,
                     bool *overall_fu_ok_out)
{
  const tic6x_opcode *opc_entry = &tic6x_opcode_table[id];
  bool this_opc_arch_ok = true;
  bool this_opc_fu_ok = true;

  if (tic6x_insn_format_table[opc_entry->format].num_bits != 32)
    return false;

  if (!(opc_entry->isa_variants & tic6x_features))
    this_opc_arch_ok = false;
  if (opc_entry->func_unit != func_unit_base)
    this_opc_fu_ok = false;
  if (func_unit_side == 1 && (opc_entry->flags & TIC6X_FLAG_SIDE_B_ONLY))
    this_opc_fu_ok = false;
  if (func_unit_cross && (opc_entry->flags & TIC6X_FLAG_NO_CROSS))
    this_opc_fu_ok = false;
  if (!func_unit_data_side && (opc_entry->flags & (TIC6X_FLAG_LOAD | TIC6X_FLAG_STORE)))
    this_opc_fu_ok = false;
  if (func_unit_data_side && !(opc_entry->flags & (TIC6X_FLAG_LOAD | TIC6X_FLAG_STORE)))
    this_opc_fu_ok = false;
  if (func_unit_data_side == 1 && (opc_entry->flags & TIC6X_FLAG_SIDE_T2_ONLY))
    this_opc_fu_ok = false;

  if (this_opc_arch_ok)
    *overall_arch_ok_out = true;
  if (this_opc_fu_ok)
    *overall_fu_ok_out = true;

  return this_opc_arch_ok && this_opc_fu_ok;
}

static tic6x_opcode_id *
collect_matching_opcodes_and_forms(tic6x_opcode_list *opc_list_head,
                                   tic6x_func_unit_base func_unit_base,
                                   unsigned int func_unit_side,
                                   unsigned int func_unit_cross,
                                   unsigned int func_unit_data_side,
                                   unsigned int *num_matching_opcodes_out,
                                   unsigned int *max_num_operands_out,
                                   unsigned int operand_forms[TIC6X_MAX_SOURCE_OPERANDS],
                                   bool num_operands_permitted[TIC6X_MAX_SOURCE_OPERANDS + 1],
                                   const char *opc_str, int opc_len)
{
  unsigned int max_possible_opcodes = 0;
  for (tic6x_opcode_list *opc = opc_list_head; opc; opc = opc->next)
    max_possible_opcodes++;

  if (max_possible_opcodes == 0)
    {
      as_bad(_("internal error: no opcodes in list"));
      return NULL;
    }

  tic6x_opcode_id *opcm = XNEWVEC(tic6x_opcode_id, max_possible_opcodes);
  if (opcm == NULL)
    {
      as_bad(_("memory allocation failed"));
      return NULL;
    }

  *num_matching_opcodes_out = 0;
  *max_num_operands_out = 0;
  bool ok_this_arch = false;
  bool ok_this_fu = false;
  bool ok_this_arch_fu = false;

  memset(operand_forms, 0, sizeof(unsigned int) * TIC6X_MAX_SOURCE_OPERANDS);
  memset(num_operands_permitted, 0, sizeof(bool) * (TIC6X_MAX_SOURCE_OPERANDS + 1));

  for (tic6x_opcode_list *opc = opc_list_head; opc; opc = opc->next)
    {
      if (is_opcode_compatible(opc->id, func_unit_base, func_unit_side,
                               func_unit_cross, func_unit_data_side,
                               &ok_this_arch, &ok_this_fu))
        {
          ok_this_arch_fu = true;
          opcm[*num_matching_opcodes_out] = opc->id;
          (*num_matching_opcodes_out)++;

          const tic6x_opcode *opc_entry = &tic6x_opcode_table[opc->id];
          unsigned int num_operands_for_this_opc = opc_entry->num_operands;

          if (opc_entry->flags & TIC6X_FLAG_SPMASK)
            {
              if (num_operands_for_this_opc != 1 || (opc_entry->operand_info[0].form != tic6x_operand_func_unit))
                abort();

              num_operands_for_this_opc = 8;
              for (unsigned int i = 0; i < num_operands_for_this_opc; i++)
                {
                  operand_forms[i] |= tic6x_coarse_operand_form(tic6x_operand_func_unit);
                  num_operands_permitted[i] = true;
                }
            }
          else
            {
              for (unsigned int i = 0; i < num_operands_for_this_opc; i++)
                {
                  operand_forms[i] |= tic6x_coarse_operand_form(opc_entry->operand_info[i].form);
                }
            }
          num_operands_permitted[num_operands_for_this_opc] = true;
          if (num_operands_for_this_opc > *max_num_operands_out)
            *max_num_operands_out = num_operands_for_this_opc;
        }
    }

  if (!ok_this_arch)
    {
      as_bad(_("'%.*s' instruction not supported on this architecture"), opc_len, opc_str);
      free(opcm);
      return NULL;
    }
  if (!ok_this_fu)
    {
      as_bad(_("'%.*s' instruction not supported on this functional unit"), opc_len, opc_str);
      free(opcm);
      return NULL;
    }
  if (!ok_this_arch_fu)
    {
      as_bad(_("'%.*s' instruction not supported on this functional unit for this architecture"), opc_len, opc_str);
      free(opcm);
      return NULL;
    }

  if (*num_matching_opcodes_out == 0)
    {
      as_bad(_("internal error: no matching opcodes after checks for '%.*s'"), opc_len, opc_str);
      free(opcm);
      return NULL;
    }

  return opcm;
}

static bool
parse_all_operands(const char **p_ptr,
                   tic6x_operand operands[TIC6X_MAX_SOURCE_OPERANDS],
                   unsigned int operand_forms[TIC6X_MAX_SOURCE_OPERANDS],
                   unsigned int max_num_operands,
                   unsigned int *num_operands_read_out,
                   const char *opc_str, int opc_len,
                   const bool num_operands_permitted[TIC6X_MAX_SOURCE_OPERANDS + 1])
{
  const char *p = *p_ptr;
  *num_operands_read_out = 0;

  while (true)
    {
      skip_whitespace(p);
      if (is_end_of_stmt(*p))
        {
          if (*num_operands_read_out > 0 && max_num_operands > 0 && !is_end_of_stmt(*(p -1)) && *(p-1) == ',')
            {
              as_bad(_("missing operand after comma"));
              return false;
            }
          break;
        }

      if (*num_operands_read_out >= TIC6X_MAX_SOURCE_OPERANDS)
        {
          as_bad(_("too many operands to '%.*s' (max %u)"), opc_len, opc_str, TIC6X_MAX_SOURCE_OPERANDS);
          return false;
        }

      if (*num_operands_read_out >= max_num_operands && max_num_operands != 0)
        {
            as_bad (_("too many operands to '%.*s'"), opc_len, opc_str);
            return false;
        }

      if (!tic6x_parse_operand(&p, &operands[*num_operands_read_out],
                               operand_forms[*num_operands_read_out],
                               opc_str, opc_len, *num_operands_read_out + 1))
        {
          return false;
        }
      (*num_operands_read_out)++;

      if (is_end_of_stmt(*p))
        break;
      else if (*p == ',')
        {
          p++;
          if (*num_operands_read_out == max_num_operands && max_num_operands != 0)
            {
              as_bad(_("too many operands to '%.*s'"), opc_len, opc_str);
              return false;
            }
          continue;
        }
      else
        {
          as_bad(_("syntax error after operand %u for '%.*s'"), *num_operands_read_out, opc_len, opc_str);
          return false;
        }
    }

  if (!num_operands_permitted[*num_operands_read_out])
    {
      as_bad(_("bad number of operands (%u) to '%.*s'"), *num_operands_read_out, opc_len, opc_str);
      return false;
    }

  *p_ptr = p;
  return true;
}

static bool
validate_detailed_operands(const tic6x_operand operands[TIC6X_MAX_SOURCE_OPERANDS],
                           unsigned int num_operands_read,
                           const tic6x_opcode_id *opcm,
                           unsigned int num_matching_opcodes,
                           unsigned int func_unit_side,
                           unsigned int cross_side,
                           unsigned int func_unit_data_side,
                           const char *opc_str, int opc_len)
{
  for (unsigned int i = 0; i < num_operands_read; i++)
    {
      bool fine_ok = false;
      tic6x_operand_match fine_failure = tic6x_match_matches;

      for (unsigned int j = 0; j < num_matching_opcodes; j++)
        {
          const tic6x_opcode *opc_entry = &tic6x_opcode_table[opcm[j]];
          tic6x_operand_form f;
          tic6x_rw rw;

          if (opc_entry->flags & TIC6X_FLAG_SPMASK)
            {
              f = tic6x_operand_func_unit;
              rw = tic6x_rw_none;
            }
          else
            {
              if (opc_entry->num_operands != num_operands_read)
                continue;

              f = opc_entry->operand_info[i].form;
              rw = opc_entry->operand_info[i].rw;
            }

          if (operands[i].form != tic6x_coarse_operand_form(f))
            continue;

          tic6x_operand_match this_fine_failure
            = tic6x_operand_matches_form(&operands[i], f, rw,
                                         func_unit_side,
                                         cross_side,
                                         func_unit_data_side);
          if (this_fine_failure == tic6x_match_matches)
            {
              fine_ok = true;
              break;
            }
          if (fine_failure == tic6x_match_matches || fine_failure > this_fine_failure)
            fine_failure = this_fine_failure;
        }

      if (!fine_ok)
        {
          switch (fine_failure)
            {
            case tic6x_match_non_const:
              as_bad(_("operand %u of '%.*s' not constant"), i + 1, opc_len, opc_str);
              break;
            case tic6x_match_wrong_side:
              as_bad(_("operand %u of '%.*s' on wrong side"), i + 1, opc_len, opc_str);
              break;
            case tic6x_match_bad_return:
              as_bad(_("operand %u of '%.*s' not a valid return address register"), i + 1, opc_len, opc_str);
              break;
            case tic6x_match_ctrl_write_only:
              as_bad(_("operand %u of '%.*s' is write-only"), i + 1, opc_len, opc_str);
              break;
            case tic6x_match_ctrl_read_only:
              as_bad(_("operand %u of '%.*s' is read-only"), i + 1, opc_len, opc_str);
              break;
            case tic6x_match_bad_mem:
              as_bad(_("operand %u of '%.*s' not a valid memory reference"), i + 1, opc_len, opc_str);
              break;
            case tic6x_match_bad_address:
              as_bad(_("operand %u of '%.*s' not a valid base address register"), i + 1, opc_len, opc_str);
              break;
            case tic6x_match_matches:
            default:
              abort();
            }
          return false;
        }
    }
  return true;
}

static bool
select_and_encode_opcode(const tic6x_opcode_id *opcm,
                         unsigned int num_matching_opcodes,
                         const tic6x_operand operands[TIC6X_MAX_SOURCE_OPERANDS],
                         unsigned int num_operands_read,
                         unsigned int this_line_creg,
                         unsigned int this_line_z,
                         unsigned int func_unit_side,
                         unsigned int func_unit_cross,
                         unsigned int func_unit_data_side,
                         unsigned int sploop_ii,
                         unsigned int *opcode_value_out,
                         const tic6x_opcode **opct_out,
                         expressionS **fix_exp_out,
                         int *fix_pcrel_out,
                         bfd_reloc_code_real_type *fx_r_type_out,
                         bool *fix_adda_out,
                         bool *fix_needed_out,
                         const char *opc_str, int opc_len)
{
  unsigned int opc_rank[TIC6X_NUM_PREFER];
  for (unsigned int i = 0; i < TIC6X_NUM_PREFER; i++)
    opc_rank[i] = -1u;

  int min_rank = TIC6X_NUM_PREFER - 1;
  int max_rank = 0;
  bool found_match_for_operands = false;

  for (unsigned int i = 0; i < num_matching_opcodes; i++)
    {
      const tic6x_opcode *opc_entry = &tic6x_opcode_table[opcm[i]];
      bool this_matches_all_operands = true;

      if (!(opc_entry->flags & TIC6X_FLAG_SPMASK) && opc_entry->num_operands != num_operands_read)
        continue;

      for (unsigned int j = 0; j < num_operands_read; j++)
        {
          tic6x_operand_form f;
          tic6x_rw rw;

          if (opc_entry->flags & TIC6X_FLAG_SPMASK)
            {
              f = tic6x_operand_func_unit;
              rw = tic6x_rw_none;
            }
          else
            {
              f = opc_entry->operand_info[j].form;
              rw = opc_entry->operand_info[j].rw;
            }

          if (tic6x_operand_matches_form(&operands[j], f, rw,
                                         func_unit_side,
                                         cross_side,
                                         func_unit_data_side)
              != tic6x_match_matches)
            {
              this_matches_all_operands = false;
              break;
            }
        }

      if (this_matches_all_operands)
        {
          int rank = TIC6X_PREFER_VAL(opc_entry->flags);
          if (rank < min_rank) min_rank = rank;
          if (rank > max_rank) max_rank = rank;

          if (opc_rank[rank] == -1u)
            opc_rank[rank] = i;
          else
            {
              abort();
            }
          found_match_for_operands = true;
        }
    }

  if (!found_match_for_operands)
    {
      as_bad(_("bad operand combination for '%.*s'"), opc_len, opc_str);
      return false;
    }

  bool encoded_ok = false;
  for (int try_rank = max_rank; try_rank >= min_rank; try_rank--)
    {
      if (opc_rank[try_rank] == -1u)
        continue;

      *fix_needed_out = false;

      *opcode_value_out = tic6x_try_encode(opcm[opc_rank[try_rank]],
                                           operands, num_operands_read,
                                           this_line_creg, this_line_z,
                                           func_unit_side, func_unit_cross,
                                           func_unit_data_side, sploop_ii,
                                           fix_exp_out, fix_pcrel_out,
                                           fx_r_type_out, fix_adda_out,
                                           fix_needed_out, &encoded_ok,
                                           try_rank == min_rank,
                                           opc_str, opc_len);
      if (encoded_ok)
        {
          *opct_out = &tic6x_opcode_table[opcm[opc_rank[try_rank]]];
          return true;
        }
    }

  return false;
}

static fragS *
handle_instruction_frag_creation(bool this_line_parallel,
                                 segment_info_type *seginfo,
                                 tic6x_label_list *this_insn_label_list,
                                 const char *opc_str, int opc_len,
                                 const tic6x_opcode *opct,
                                 char **output_ptr_out)
{
  fragS *insn_frag;
  if (this_line_parallel)
    {
      insn_frag = seginfo->tc_segment_info_data.execute_packet_frag;
      if (insn_frag == NULL)
        {
          as_bad(_("parallel instruction not following another instruction"));
          return NULL;
        }

      if (insn_frag->fr_fix >= 32)
        {
          as_bad(_("too many instructions in execute packet"));
          return NULL;
        }

      if (this_insn_label_list != NULL)
        as_bad(_("label not at start of execute packet"));

      if (opct->flags & TIC6X_FLAG_FIRST)
        as_bad(_("'%.*s' instruction not at start of execute packet"), opc_len, opc_str);

      *seginfo->tc_segment_info_data.last_insn_lsb |= 0x1;
      *output_ptr_out = insn_frag->fr_literal + insn_frag->fr_fix;
    }
  else
    {
      seginfo->tc_segment_info_data.spmask_addr = NULL;
      seginfo->tc_segment_info_data.func_units_used = 0;

      if (frag_now_fix() != 0)
        {
          if (frag_now->fr_type != rs_machine_dependent)
            frag_wane(frag_now);
          frag_new(0);
        }
      frag_grow(32);
      insn_frag = seginfo->tc_segment_info_data.execute_packet_frag = frag_now;

      for (tic6x_label_list *l = this_insn_label_list; l; l = l->next)
        {
          symbol_set_frag(l->label, frag_now);
          S_SET_VALUE(l->label, 0);
          S_SET_SEGMENT(l->label, now_seg);
        }
      tic6x_free_label_list(this_insn_label_list);

      dwarf2_emit_insn(0);
      *output_ptr_out = frag_var(rs_machine_dependent, 32, 32, 0, NULL, 0, NULL);

      if (*output_ptr_out != insn_frag->fr_literal)
        abort();

      insn_frag->tc_frag_data.is_insns = true;
      insn_frag->tc_frag_data.can_cross_fp_boundary = tic6x_can_cross_fp_boundary;
    }
  return insn_frag;
}

static void
handle_spmask_and_sploop_flags(const tic6x_opcode *opct,
                               const tic6x_operand operands[TIC6X_MAX_SOURCE_OPERANDS],
                               unsigned int num_operands_read,
                               bool this_line_spmask,
                               tic6x_func_unit_base func_unit_base,
                               unsigned int func_unit_side,
                               segment_info_type *seginfo,
                               const char *opc_str, int opc_len)
{
  if (func_unit_base != tic6x_func_unit_nfu)
    {
      unsigned int func_unit_enc = tic6x_encode_spmask(func_unit_base, func_unit_side);
      if (seginfo->tc_segment_info_data.func_units_used & func_unit_enc)
        as_bad(_("functional unit already used in this execute packet"));
      seginfo->tc_segment_info_data.func_units_used |= func_unit_enc;
    }

  if (opct->flags & TIC6X_FLAG_SPLOOP)
    {
      if (seginfo->tc_segment_info_data.sploop_ii)
        as_bad(_("nested software pipelined loop"));
      if (num_operands_read != 1
          || operands[0].form != TIC6X_OP_EXP
          || operands[0].value.exp.X_op != O_constant)
        abort();
      seginfo->tc_segment_info_data.sploop_ii = operands[0].value.exp.X_add_number;
    }
  else if (opct->flags & TIC6X_FLAG_SPKERNEL)
    {
      if (!seginfo->tc_segment_info_data.sploop_ii)
        as_bad(_("'%.*s' instruction not in a software pipelined loop"), opc_len, opc_str);
      seginfo->tc_segment_info_data.sploop_ii = 0;
    }

  if (this_line_spmask)
    {
      if (seginfo->tc_segment_info_data.spmask_addr == NULL)
        as_bad(_("'||^' without previous SPMASK"));
      else if (func_unit_base == tic6x_func_unit_nfu)
        as_bad(_("cannot mask instruction using no functional unit"));
      else
        {
          unsigned int spmask_opcode = md_chars_to_number(seginfo->tc_segment_info_data.spmask_addr, 4);
          unsigned int mask_bit = tic6x_encode_spmask(func_unit_base, func_unit_side);
          mask_bit <<= 18;
          if (spmask_opcode & mask_bit)
            as_bad(_("functional unit already masked"));
          spmask_opcode |= mask_bit;
          md_number_to_chars(seginfo->tc_segment_info_data.spmask_addr, spmask_opcode, 4);
        }
    }
}


void
md_assemble(char *str)
{
  char *p = str;
  int opc_len;
  segment_info_type *seginfo;

  bool this_line_parallel = tic6x_line_parallel;
  bool this_line_spmask = tic6x_line_spmask;
  unsigned int this_line_creg = tic6x_line_creg;
  unsigned int this_line_z = tic6x_line_z;

  tic6x_line_parallel = false;
  tic6x_line_spmask = false;
  tic6x_line_creg = 0;
  tic6x_line_z = 0;

  seginfo = seg_info(now_seg);
  tic6x_label_list *this_insn_label_list = seginfo->tc_segment_info_data.label_list;
  seginfo->tc_segment_info_data.label_list = NULL;

  const char *opc_name_start = parse_opcode_name(str, &opc_len);
  if (opc_name_start == NULL)
    return;

  tic6x_seen_insns = true;
  if (tic6x_arch_attribute == C6XABI_Tag_ISA_none)
    tic6x_arch_attribute = C6XABI_Tag_ISA_C674X;

  tic6x_opcode_list *opc_list = str_hash_find_n(opcode_hash, opc_name_start, opc_len);
  if (opc_list == NULL)
    {
      char c = p[opc_len];
      *((char*)opc_name_start + opc_len) = 0;
      as_bad(_("unknown opcode '%s'"), opc_name_start);
      *((char*)opc_name_start + opc_len) = c;
      return;
    }
  p += opc_len;

  skip_whitespace(p);

  tic6x_func_unit_base func_unit_base = tic6x_func_unit_nfu;
  unsigned int func_unit_side = 0;
  unsigned int func_unit_cross = 0;
  unsigned int cross_side = 0;
  unsigned int func_unit_data_side = 0;

  parse_functional_unit_specifier(&p, &func_unit_base, &func_unit_side,
                                  &func_unit_cross, &cross_side, &func_unit_data_side);
  skip_whitespace(p);

  unsigned int num_matching_opcodes;
  unsigned int max_num_operands;
  unsigned int operand_forms[TIC6X_MAX_SOURCE_OPERANDS];
  bool num_operands_permitted[TIC6X_MAX_SOURCE_OPERANDS + 1];

  tic6x_opcode_id *opcm = collect_matching_opcodes_and_forms(opc_list,
                                                             func_unit_base,
                                                             func_unit_side,
                                                             func_unit_cross,
                                                             func_unit_data_side,
                                                             &num_matching_opcodes,
                                                             &max_num_operands,
                                                             operand_forms,
                                                             num_operands_permitted,
                                                             opc_name_start, opc_len);
  if (opcm == NULL)
    return;

  tic6x_operand operands[TIC6X_MAX_SOURCE_OPERANDS];
  unsigned int num_operands_read;

  if (!parse_all_operands(&p, operands, operand_forms, max_num_operands,
                          &num_operands_read, opc_name_start, opc_len, num_operands_permitted))
    {
      free(opcm);
      return;
    }

  if (!validate_detailed_operands(operands, num_operands_read, opcm, num_matching_opcodes,
                                  func_unit_side, cross_side, func_unit_data_side,
                                  opc_name_start, opc_len))
    {
      free(opcm);
      return;
    }

  unsigned int opcode_value;
  const tic6x_opcode *opct = NULL;
  expressionS *fix_exp = NULL;
  int fix_pcrel = 0;
  bfd_reloc_code_real_type fx_r_type = BFD_RELOC_UNUSED;
  bool fix_adda = false;
  bool fix_needed = false;

  if (!select_and_encode_opcode(opcm, num_matching_opcodes, operands, num_operands_read,
                                this_line_creg, this_line_z, func_unit_side, func_unit_cross,
                                func_unit_data_side, seginfo->tc_segment_info_data.sploop_ii,
                                &opcode_value, &opct, &fix_exp, &fix_pcrel, &fx_r_type,
                                &fix_adda, &fix_needed, opc_name_start, opc_len))
    {
      free(opcm);
      return;
    }

  free(opcm);

  fragS *insn_frag;
  char *output;
  insn_frag = handle_instruction_frag_creation(this_line_parallel, seginfo,
                                               this_insn_label_list,
                                               opc_name_start, opc_len,
                                               opct, &output);
  if (insn_frag == NULL)
    return;

  handle_spmask_and_sploop_flags(opct, operands, num_operands_read,
                                 this_line_spmask, func_unit_base, func_unit_side,
                                 seginfo, opc_name_start, opc_len);

  record_alignment(now_seg, 5);
  md_number_to_chars(output, opcode_value, 4);

  if (fix_needed)
    tic6x_fix_new_exp(insn_frag, output - insn_frag->fr_literal, 4, fix_exp,
                      fix_pcrel, fx_r_type, fix_adda);

  insn_frag->fr_fix += 4;
  insn_frag->fr_var -= 4;
  seginfo->tc_segment_info_data.last_insn_lsb = (target_big_endian ? output + 3 : output);

  if (opct->flags & TIC6X_FLAG_SPMASK)
    seginfo->tc_segment_info_data.spmask_addr = output;
}

/* Modify NEWVAL (32-bit) by inserting VALUE, shifted right by SHIFT
   and the least significant BITS bits taken, at position POS.  */
#define MODIFY_VALUE(NEWVAL, VALUE, SHIFT, POS, BITS)			\
  do {									\
    (NEWVAL) &= 0xffffffffU & ~(((1U << (BITS)) - 1) << (POS));		\
    (NEWVAL) |= (((VALUE) >> (SHIFT)) & ((1U << (BITS)) - 1)) << (POS);	\
  } while (0)

/* Apply a fixup to the object file.  */

void
md_apply_fix (fixS *fixP, valueT *valP, const segT seg ATTRIBUTE_UNUSED)
{
  valueT value = *valP;
  char *buf = fixP->fx_where + fixP->fx_frag->fr_literal;

  const valueT UNSIGNED_8_BIT_MAX = 0xFF;
  const valueT UNSIGNED_16_BIT_MAX = 0xFFFF;
  const valueT SIGNED_16_BIT_MAX = 0x7FFF;

  const valueT ALIGN_2_BYTE_MASK = 0x1;
  const valueT ALIGN_4_BYTE_MASK = 0x3;

  const valueT RELOC_8_SIGNED_OFFSET = 0x80;
  const valueT RELOC_16_SIGNED_OFFSET = 0x8000;
  const valueT C6000_PCR_S7_SIGNED_OFFSET = 0x100;
  const valueT C6000_PCR_S10_SIGNED_OFFSET = 0x800;
  const valueT C6000_PCR_S12_SIGNED_OFFSET = 0x2000;
  const valueT C6000_PCR_S21_SIGNED_OFFSET = 0x400000;

  value = SEXT (value);
  *valP = value;

  fixP->fx_offset = SEXT (fixP->fx_offset);

  if (fixP->fx_addsy == NULL && fixP->fx_pcrel == 0)
    fixP->fx_done = 1;

  fixP->fx_no_overflow = 1;

  switch (fixP->fx_r_type)
    {
    case BFD_RELOC_NONE:
    case BFD_RELOC_C6000_EHTYPE:
      fixP->fx_done = 0;
      break;

    case BFD_RELOC_32:
      if (fixP->fx_done || !seg->use_rela_p)
	md_number_to_chars (buf, value, 4);
      break;

    case BFD_RELOC_16:
      if (fixP->fx_done || !seg->use_rela_p)
	{
	  if (value + RELOC_16_SIGNED_OFFSET > UNSIGNED_16_BIT_MAX + RELOC_16_SIGNED_OFFSET)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("value too large for 2-byte field"));
	  md_number_to_chars (buf, value, 2);
	}
      break;

    case BFD_RELOC_8:
      if (fixP->fx_done || !seg->use_rela_p)
	{
	  if (value + RELOC_8_SIGNED_OFFSET > UNSIGNED_8_BIT_MAX + RELOC_8_SIGNED_OFFSET)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("value too large for 1-byte field"));
	  *buf = (char) value;
	}
      break;

    case BFD_RELOC_C6000_ABS_S16:
    case BFD_RELOC_C6000_ABS_L16:
    case BFD_RELOC_C6000_SBR_S16:
    case BFD_RELOC_C6000_SBR_L16_B:
    case BFD_RELOC_C6000_SBR_L16_H:
    case BFD_RELOC_C6000_SBR_L16_W:
    case BFD_RELOC_C6000_SBR_GOT_L16_W:
      if (fixP->fx_done || !seg->use_rela_p)
	{
	  valueT newval = md_chars_to_number (buf, 4);
	  int shift;

	  switch (fixP->fx_r_type)
	    {
	    case BFD_RELOC_C6000_SBR_L16_H:
	      shift = 1;
	      break;

	    case BFD_RELOC_C6000_SBR_L16_W:
	    case BFD_RELOC_C6000_SBR_GOT_L16_W:
	      shift = 2;
	      break;

	    default:
	      shift = 0;
	      break;
	    }

	  MODIFY_VALUE (newval, value, shift, 7, 16);
	  if ((value + RELOC_16_SIGNED_OFFSET > SIGNED_16_BIT_MAX + RELOC_16_SIGNED_OFFSET)
	      && (fixP->fx_r_type == BFD_RELOC_C6000_ABS_S16
		  || fixP->fx_r_type == BFD_RELOC_C6000_SBR_S16))
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("immediate offset out of range"));

	  md_number_to_chars (buf, newval, 4);
	}
      if (fixP->fx_done
	  && fixP->fx_r_type != BFD_RELOC_C6000_ABS_S16
	  && fixP->fx_r_type != BFD_RELOC_C6000_ABS_L16)
	abort ();
      break;

    case BFD_RELOC_C6000_ABS_H16:
    case BFD_RELOC_C6000_SBR_H16_B:
    case BFD_RELOC_C6000_SBR_H16_H:
    case BFD_RELOC_C6000_SBR_H16_W:
    case BFD_RELOC_C6000_SBR_GOT_H16_W:
      if (fixP->fx_done || !seg->use_rela_p)
	{
	  valueT newval = md_chars_to_number (buf, 4);
	  int shift;

	  switch (fixP->fx_r_type)
	    {
	    case BFD_RELOC_C6000_SBR_H16_H:
	      shift = 17;
	      break;

	    case BFD_RELOC_C6000_SBR_H16_W:
	    case BFD_RELOC_C6000_SBR_GOT_H16_W:
	      shift = 18;
	      break;

	    default:
	      shift = 16;
	      break;
	    }

	  MODIFY_VALUE (newval, value, shift, 7, 16);

	  md_number_to_chars (buf, newval, 4);
	}
      if (fixP->fx_done && fixP->fx_r_type != BFD_RELOC_C6000_ABS_H16)
	abort ();
      break;

    case BFD_RELOC_C6000_PCR_H16:
    case BFD_RELOC_C6000_PCR_L16:
      if (fixP->fx_done || !seg->use_rela_p)
	{
	  valueT newval = md_chars_to_number (buf, 4);
	  int shift = (fixP->fx_r_type == BFD_RELOC_C6000_PCR_H16) ? 16 : 0;

	  MODIFY_VALUE (newval, value, shift, 7, 16);

	  md_number_to_chars (buf, newval, 4);
	}
      break;

    case BFD_RELOC_C6000_SBR_U15_B:
      if (fixP->fx_done || !seg->use_rela_p)
	{
	  valueT newval = md_chars_to_number (buf, 4);
	  const valueT C6000_U15_MAX = 0x7FFF;

	  MODIFY_VALUE (newval, value, 0, 8, 15);
	  if (value > C6000_U15_MAX)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("immediate offset out of range"));

	  md_number_to_chars (buf, newval, 4);
	}
      break;

    case BFD_RELOC_C6000_SBR_U15_H:
      if (fixP->fx_done || !seg->use_rela_p)
	{
	  valueT newval = md_chars_to_number (buf, 4);
	  const valueT C6000_U15_H_MAX = 0xFFFE;

	  if (fixP->tc_fix_data.fix_adda && fixP->fx_done)
	    value <<= 1;

	  MODIFY_VALUE (newval, value, 1, 8, 15);
	  if (value & ALIGN_2_BYTE_MASK)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("immediate offset not 2-byte-aligned"));
	  if (value > C6000_U15_H_MAX)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("immediate offset out of range"));

	  md_number_to_chars (buf, newval, 4);
	}
      break;

    case BFD_RELOC_C6000_SBR_U15_W:
    case BFD_RELOC_C6000_SBR_GOT_U15_W:
      if (fixP->fx_done || !seg->use_rela_p)
	{
	  valueT newval = md_chars_to_number (buf, 4);
	  const valueT C6000_U15_W_MAX = 0x1FFFC;

	  if (fixP->tc_fix_data.fix_adda && fixP->fx_done)
	    value <<= 2;

	  MODIFY_VALUE (newval, value, 2, 8, 15);
	  if (value & ALIGN_4_BYTE_MASK)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("immediate offset not 4-byte-aligned"));
	  if (value > C6000_U15_W_MAX)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("immediate offset out of range"));

	  md_number_to_chars (buf, newval, 4);
	}
      if (fixP->fx_done && fixP->fx_r_type != BFD_RELOC_C6000_SBR_U15_W)
	abort ();
      break;

    case BFD_RELOC_C6000_DSBT_INDEX:
      if (value != 0)
	as_bad_where (fixP->fx_file, fixP->fx_line,
		      _("addend used with $DSBT_INDEX"));
      if (fixP->fx_done)
	abort ();
      break;

    case BFD_RELOC_C6000_PCR_S21:
      if (fixP->fx_done || !seg->use_rela_p)
	{
	  valueT newval = md_chars_to_number (buf, 4);
	  const valueT C6000_PCR_S21_MAX = 0x3FFFFC;

	  MODIFY_VALUE (newval, value, 2, 7, 21);

	  if (value & ALIGN_4_BYTE_MASK)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("PC-relative offset not 4-byte-aligned"));
	  if (value + C6000_PCR_S21_SIGNED_OFFSET > C6000_PCR_S21_MAX + C6000_PCR_S21_SIGNED_OFFSET)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("PC-relative offset out of range"));

	  md_number_to_chars (buf, newval, 4);
	}
      break;

    case BFD_RELOC_C6000_PCR_S12:
      if (fixP->fx_done || !seg->use_rela_p)
	{
	  valueT newval = md_chars_to_number (buf, 4);
	  const valueT C6000_PCR_S12_MAX = 0x1FFC;

	  MODIFY_VALUE (newval, value, 2, 16, 12);

	  if (value & ALIGN_4_BYTE_MASK)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("PC-relative offset not 4-byte-aligned"));
	  if (value + C6000_PCR_S12_SIGNED_OFFSET > C6000_PCR_S12_MAX + C6000_PCR_S12_SIGNED_OFFSET)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("PC-relative offset out of range"));

	  md_number_to_chars (buf, newval, 4);
	}
      break;

    case BFD_RELOC_C6000_PCR_S10:
      if (fixP->fx_done || !seg->use_rela_p)
	{
	  valueT newval = md_chars_to_number (buf, 4);
	  const valueT C6000_PCR_S10_MAX = 0x7FC;

	  MODIFY_VALUE (newval, value, 2, 13, 10);

	  if (value & ALIGN_4_BYTE_MASK)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("PC-relative offset not 4-byte-aligned"));
	  if (value + C6000_PCR_S10_SIGNED_OFFSET > C6000_PCR_S10_MAX + C6000_PCR_S10_SIGNED_OFFSET)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("PC-relative offset out of range"));

	  md_number_to_chars (buf, newval, 4);
	}
      break;

    case BFD_RELOC_C6000_PCR_S7:
      if (fixP->fx_done || !seg->use_rela_p)
	{
	  valueT newval = md_chars_to_number (buf, 4);
	  const valueT C6000_PCR_S7_MAX = 0xFC;

	  MODIFY_VALUE (newval, value, 2, 16, 7);

	  if (value & ALIGN_4_BYTE_MASK)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("PC-relative offset not 4-byte-aligned"));
	  if (value + C6000_PCR_S7_SIGNED_OFFSET > C6000_PCR_S7_MAX + C6000_PCR_S7_SIGNED_OFFSET)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("PC-relative offset out of range"));

	  md_number_to_chars (buf, newval, 4);
	}
      break;

    case BFD_RELOC_C6000_PREL31:
      fixP->fx_done = 0;
      break;

    default:
      abort ();
    }
}

/* Convert a floating-point number to target (IEEE) format.  */

const char *
md_atof (int type, char *litP, int *sizeP)
{
  if (litP == NULL || sizeP == NULL) {
    return NULL;
  }
  return ieee_md_atof (type, litP, sizeP, target_big_endian);
}

/* Adjust the frags in SECTION (see tic6x_md_finish).  */

static void tic6x_adjust_section (bfd *abfd ATTRIBUTE_UNUSED, segT section, void *dummy ATTRIBUTE_UNUSED);

#include <stdbool.h>

// Define constants for clarity and maintainability
#define ALIGN_BOUNDARY_32       32
#define ALIGN_BOUNDARY_16       16
#define ALIGN_BOUNDARY_8        8
#define INSN_SIZE_BYTES         4
#define MAX_INSNS_PER_EXEC_PKT  8
#define NOP_INSERTION_MASK      0x1

// Enum for alignment offsets for rs_align_code or similar
typedef enum {
  ALIGN_OFFSET_8_BYTE = 3,  // 2^3 = 8 bytes
  ALIGN_OFFSET_16_BYTE = 4, // 2^4 = 16 bytes
  ALIGN_OFFSET_32_BYTE = 5  // 2^5 = 32 bytes
} AlignmentOffset;

// Structure to hold state for the alignment adjustment logic
typedef struct {
  unsigned int want_insert; // NOPs we are currently looking to insert (in instructions)
  unsigned int want_insert_done_so_far; // NOPs inserted in current stage
  unsigned int current_pos_mod_32; // Position mod 32 at the start of the current frag

  // Locations of the most recent frags at which there is the given alignment.
  frchainS *frchp_last32;
  fragS *fragp_last32;
  unsigned int pos_last32;

  frchainS *frchp_last16;
  fragS *fragp_last16;
  unsigned int pos_last16;

  frchainS *frchp_last8;
  fragS *fragp_last8;
  unsigned int pos_last8;
} AlignmentState;

// Forward declarations for helper functions
static void insert_nops(fragS *fragp, unsigned int num_nops);
static void get_next_frag_and_chain(frchainS *current_frchp, fragS *current_fragp,
                                     frchainS **next_frchp_out, fragS **next_fragp_out);
static bool process_frag_for_alignment_step(fragS *fragp, AlignmentState *state, bool *did_go_back);
static void check_section_content(segment_info_type *info, bool *have_code, bool *have_non_code);
static void adjust_code_only_section_alignment(segment_info_type *info);
static void convert_machine_dependent_frags_to_generic(segment_info_type *info);

// Helper to insert NOPs, preserving the original (potentially unusual) indexing logic
static void insert_nops(fragS *fragp, unsigned int num_nops) {
  for (unsigned int i = 0; i < num_nops; ++i) {
    // Insert 4 zero bytes at the current end of the fragment
    md_number_to_chars(fragp->fr_literal + fragp->fr_fix, 0, INSN_SIZE_BYTES);

    // Apply the NOP_INSERTION_MASK. This modifies a byte *before* the newly inserted data.
    // This behaviour is preserved from the original code.
    if (target_big_endian) {
      fragp->fr_literal[fragp->fr_fix - 1] |= NOP_INSERTION_MASK;
    } else {
      fragp->fr_literal[fragp->fr_fix - INSN_SIZE_BYTES] |= NOP_INSERTION_MASK;
    }

    // Update fragment size and variable data to reflect the inserted NOP
    fragp->fr_fix += INSN_SIZE_BYTES;
    fragp->fr_var -= INSN_SIZE_BYTES;
  }
}

// Helper to determine next frag/frchain for alignment history updates
static void get_next_frag_and_chain(frchainS *current_frchp, fragS *current_fragp,
                                     frchainS **next_frchp_out, fragS **next_fragp_out) {
  *next_frchp_out = current_frchp;
  *next_fragp_out = current_fragp->fr_next;

  if (*next_fragp_out == NULL) {
    *next_frchp_out = current_frchp->frch_next;
    if (*next_frchp_out != NULL) {
      *next_fragp_out = (*next_frchp_out)->frch_root;
    }
  }
}

// This function processes a single frag, potentially modifying it and the state.
// Returns true on an abort condition, false otherwise. Sets did_go_back if a rewind is necessary.
static bool process_frag_for_alignment_step(fragS *fragp, AlignmentState *state, bool *did_go_back) {
  *did_go_back = false;

  if (fragp->fr_type != rs_machine_dependent) {
    return false; // Only machine-dependent frags are relevant
  }

  // Handle alignment requirement not met or crossing boundary for instruction fragments
  if (fragp->tc_frag_data.is_insns && (state->current_pos_mod_32 + fragp->fr_fix > ALIGN_BOUNDARY_32) && !fragp->tc_frag_data.can_cross_fp_boundary) {
    if (state->want_insert) abort();
    if (state->current_pos_mod_32 & (INSN_SIZE_BYTES - 1)) abort();
    state->want_insert = (ALIGN_BOUNDARY_32 - state->current_pos_mod_32) / INSN_SIZE_BYTES;
    if (state->want_insert > 7) abort();
    state->want_insert_done_so_far = 0;
    *did_go_back = true;
    return false;
  }

  // Handle non-instruction machine-dependent fragments (e.g., alignment directives)
  if (!fragp->tc_frag_data.is_insns) {
    unsigned int required_alignment_bytes = (1U << fragp->fr_offset);
    if (!(state->current_pos_mod_32 & (required_alignment_bytes - 1))) {
      return false; // This alignment requirement is already met
    }

    if (state->want_insert) abort();

    unsigned int would_insert_bytes = required_alignment_bytes - (state->current_pos_mod_32 & (required_alignment_bytes - 1));

    if (fragp->fr_subtype != 0 && would_insert_bytes > fragp->fr_subtype) {
      return false; // Cannot meet requirement within subtype limit
    }

    if (fragp->fr_offset != ALIGN_OFFSET_8_BYTE &&
        fragp->fr_offset != ALIGN_OFFSET_16_BYTE &&
        fragp->fr_offset != ALIGN_OFFSET_32_BYTE) {
      abort();
    }

    if (would_insert_bytes & (INSN_SIZE_BYTES - 1)) abort();
    state->want_insert = would_insert_bytes / INSN_SIZE_BYTES;
    if (state->want_insert > 7) abort();
    state->want_insert_done_so_far = 0;
    *did_go_back = true;
    return false;
  }

  // If NOP insertion is active and we are processing a code frag
  if (state->want_insert && !(*did_go_back)) {
    unsigned int num_insns_in_frag = fragp->fr_fix / INSN_SIZE_BYTES;
    unsigned int max_poss_nops = MAX_INSNS_PER_EXEC_PKT - num_insns_in_frag;

    if (max_poss_nops > 0) {
      unsigned int current_stage_want_nops;
      if (state->want_insert & 1) {
          current_stage_want_nops = 1;
      } else if (state->want_insert & 2) {
          current_stage_want_nops = 2;
      } else if (state->want_insert & 4) {
          current_stage_want_nops = 4;
      } else {
          abort();
      }

      unsigned int remaining_for_stage = current_stage_want_nops - state->want_insert_done_so_far;
      unsigned int nops_to_insert = (max_poss_nops < remaining_for_stage) ? max_poss_nops : remaining_for_stage;

      insert_nops(fragp, nops_to_insert);

      state->want_insert_done_so_far += nops_to_insert;
      if (state->want_insert_done_so_far == current_stage_want_nops) {
        state->want_insert -= current_stage_want_nops;
        state->want_insert_done_so_far = 0;
        if (state->want_insert) {
          *did_go_back = true;
        }
      }
    }
  }

  return false;
}

// Initial scan to determine if the section contains code and/or non-code
static void check_section_content(segment_info_type *info, bool *have_code, bool *have_non_code) {
  *have_code = false;
  *have_non_code = false;

  for (frchainS *frchp = info->frchainP; frchp; frchp = frchp->frch_next) {
    for (fragS *fragp = frchp->frch_root; fragp; fragp = fragp->fr_next) {
      switch (fragp->fr_type) {
        case rs_machine_dependent:
          if (fragp->tc_frag_data.is_insns) {
            *have_code = true;
          }
          break;
        case rs_dummy:
        case rs_fill:
          if (fragp->fr_fix > 0) {
            *have_non_code = true;
          }
          break;
        default:
          *have_non_code = true;
          break;
      }
      if (*have_code && *have_non_code) {
        return; // Found both, no need to continue scanning
      }
    }
  }
}

// Main logic for adjusting alignment in code-only sections
static void adjust_code_only_section_alignment(segment_info_type *info) {
  AlignmentState state = {0};

  // Initialize state with first frag's info if available
  if (info->frchainP == NULL || info->frchainP->frch_root == NULL) {
    return; // Empty section, no adjustment needed
  }

  state.frchp_last32 = state.frchp_last16 = state.frchp_last8 = info->frchainP;
  state.fragp_last32 = state.fragp_last16 = state.fragp_last8 = info->frchainP->frch_root;
  state.pos_last32 = state.pos_last16 = state.pos_last8 = 0;
  state.current_pos_mod_32 = 0;

  frchainS *current_frchp = info->frchainP;
  fragS *current_fragp = info->frchainP->frch_root;

  while (current_frchp != NULL) {
    while (current_fragp != NULL) {
      bool did_go_back = false;
      if (process_frag_for_alignment_step(current_fragp, &state, &did_go_back)) {
        return; // Abort condition met inside helper
      }

      if (did_go_back) {
        // Reset iterators based on `want_insert` from state.
        if (state.want_insert & 1) {
          current_frchp = state.frchp_last8;
          current_fragp = state.fragp_last8;
          state.current_pos_mod_32 = state.pos_last8;
        } else if (state.want_insert & 2) {
          current_frchp = state.frchp_last16;
          current_fragp = state.fragp_last16;
          state.current_pos_mod_32 = state.pos_last16;
        } else if (state.want_insert & 4) {
          current_frchp = state.frchp_last32;
          current_fragp = state.fragp_last32;
          state.current_pos_mod_32 = state.pos_last32;
        } else {
          abort(); // Should not happen if `want_insert` is set and not 1, 2, or 4
        }
        continue; // Restart inner loop with the reset frag
      }

      // If no go_back, update current_pos_mod_32 and alignment history, then advance to next frag
      state.current_pos_mod_32 = (state.current_pos_mod_32 + current_fragp->fr_fix) % ALIGN_BOUNDARY_32;

      frchainS *next_frchp_candidate;
      fragS *next_fragp_candidate;
      get_next_frag_and_chain(current_frchp, current_fragp, &next_frchp_candidate, &next_fragp_candidate);

      if (!(state.current_pos_mod_32 & (ALIGN_BOUNDARY_8 - 1))) {
        state.frchp_last8 = next_frchp_candidate;
        state.fragp_last8 = next_fragp_candidate;
        state.pos_last8 = state.current_pos_mod_32;
      }
      if (!(state.current_pos_mod_32 & (ALIGN_BOUNDARY_16 - 1))) {
        state.frchp_last16 = next_frchp_candidate;
        state.fragp_last16 = next_fragp_candidate;
        state.pos_last16 = state.current_pos_mod_32;
      }
      if (!(state.current_pos_mod_32 & (ALIGN_BOUNDARY_32 - 1))) {
        state.frchp_last32 = next_frchp_candidate;
        state.fragp_last32 = next_fragp_candidate;
        state.pos_last32 = state.current_pos_mod_32;
      }

      // Advance to the next frag in the normal sequence
      current_fragp = current_fragp->fr_next;
      if (current_fragp == NULL) {
        current_frchp = current_frchp->frch_next;
        if (current_frchp != NULL) {
          current_fragp = current_frchp->frch_root;
        }
      }
    }
  }
}

// Convert machine-dependent fragments to generic types
static void convert_machine_dependent_frags_to_generic(segment_info_type *info) {
  for (frchainS *frchp = info->frchainP; frchp; frchp = frchp->frch_next) {
    for (fragS *fragp = frchp->frch_root; fragp; fragp = fragp->fr_next) {
      if (fragp->fr_type == rs_machine_dependent) {
        if (fragp->tc_frag_data.is_insns) {
          frag_wane(fragp);
        } else {
          fragp->fr_type = rs_align_code;
          fragp->fr_var = 1;
          if (fragp->fr_literal != NULL) {
              *fragp->fr_literal = 0;
          }
        }
      }
    }
  }
}

static void
tic6x_adjust_section (bfd *abfd ATTRIBUTE_UNUSED, segT section,
		      void *dummy ATTRIBUTE_UNUSED)
{
  segment_info_type *info = seg_info (section);
  if (info == NULL) {
    return;
  }

  bool have_code;
  bool have_non_code;
  check_section_content(info, &have_code, &have_non_code);

  // Process alignment requirements only in a code-only section.
  if (have_code && !have_non_code) {
    adjust_code_only_section_alignment(info);
  }

  // Now convert the machine-dependent frags to machine-independent ones.
  convert_machine_dependent_frags_to_generic(info);
}

/* Initialize the machine-dependent parts of a frag.  */

void
tic6x_frag_init (fragS *fragp)
{
  if (fragp == NULL)
    {
      return;
    }
  fragp->tc_frag_data.is_insns = false;
  fragp->tc_frag_data.can_cross_fp_boundary = false;
}

/* Set an attribute if it has not already been set by the user.  */

static void
tic6x_set_attribute_int (int tag, int value)
{
  if (tag < 1 || tag >= NUM_KNOWN_OBJ_ATTRIBUTES)
    {
      as_fatal (_("internal error: invalid attribute tag %d"), tag);
    }

  if (!tic6x_attributes_set_explicitly[tag])
    {
      if (!bfd_elf_add_proc_attr_int (stdoutput, tag, value))
        {
          as_fatal (_("error adding attribute: %s"),
                    bfd_errmsg (bfd_get_error ()));
        }
    }
}

/* Set object attributes deduced from the input file and command line
   rather than given explicitly.  */
static void
tic6x_set_attributes (void)
{
  if (tic6x_arch_attribute == C6XABI_Tag_ISA_none)
    tic6x_arch_attribute = C6XABI_Tag_ISA_C674X;

  struct {
      int tag;
      int value;
  } attribute_settings[] = {
      {Tag_ISA, tic6x_arch_attribute},
      {Tag_ABI_DSBT, tic6x_dsbt},
      {Tag_ABI_PID, tic6x_pid},
      {Tag_ABI_PIC, tic6x_pic}
  };

  for (size_t i = 0; i < sizeof(attribute_settings) / sizeof(attribute_settings[0]); ++i)
    {
      tic6x_set_attribute_int(attribute_settings[i].tag, attribute_settings[i].value);
    }
}

/* Do machine-dependent manipulations of the frag chains after all
   input has been read and before the machine-independent sizing and
   relaxing.  */

void
tic6x_md_finish (void)
{
  tic6x_set_attributes ();

  if (!bfd_map_over_sections (stdoutput, tic6x_adjust_section, NULL))
    {
      _bfd_fatal_error (bfd_errmsg ());
    }
}

/* No machine-dependent frags at this stage; all converted in
   tic6x_md_finish.  */

#include <stdio.h>
#include <stdlib.h>

// Assume ATTRIBUTE_UNUSED, bfd, and segT are defined in other headers
// as per the legacy codebase context.

void
md_convert_frag (bfd *abfd ATTRIBUTE_UNUSED, segT asec ATTRIBUTE_UNUSED,
		 fragS *fragp ATTRIBUTE_UNUSED)
{
  // This function serves as a placeholder for architecture-specific or
  // context-specific fragment conversion logic that is either not yet
  // implemented, not supported, or not expected to be called in the
  // current build configuration.
  //
  // Calling this function indicates a critical internal error, implying
  // a missing implementation, an incorrect program flow, or an unsupported
  // operational mode. Termination via abort() is consistent with the original
  // functionality, ensuring immediate cessation of execution for an unrecoverable
  // internal state. The added logging provides crucial context for debugging
  // and maintainability.
  fprintf(stderr, "FATAL ERROR: md_convert_frag was invoked for an "
                  "unsupported or unimplemented configuration.\n"
                  "This indicates an unrecoverable internal state or a "
                  "missing component for the current setup.\n"
                  "The program will now terminate to prevent further issues.\n");
  fflush(stderr); // Ensure the diagnostic message is written to stderr before terminating.
  abort();        // Terminate the program abnormally, consistent with original behavior.
}

/* No machine-dependent frags at this stage; all converted in
   tic6x_md_finish.  */

#include <stdlib.h>
#include <stdio.h>

int
md_estimate_size_before_relax (fragS *fragp ATTRIBUTE_UNUSED,
			       segT seg ATTRIBUTE_UNUSED)
{
  fprintf(stderr, "FATAL ERROR: md_estimate_size_before_relax was called. This function is a placeholder and should not be invoked in the current system state.\n");
  abort();
}

/* Put a number into target byte order.  */

void
md_number_to_chars (char *buf, valueT val, int n)
{
  if (buf == 0)
    {
      return;
    }

  if (n <= 0)
    {
      return;
    }

  if (target_big_endian)
    number_to_chars_bigendian (buf, val, n);
  else
    number_to_chars_littleendian (buf, val, n);
}

/* Machine-dependent operand parsing not currently needed.  */

void
md_operand (expressionS *op ATTRIBUTE_UNUSED)
{
  (void)op;
}

/* PC-relative operands are relative to the start of the fetch
   packet.  */

long
tic6x_pcrel_from_section (fixS *fixp, segT sec)
{
  if (fixp == NULL)
    return 0;

  if (fixp->fx_frag == NULL)
    return 0;

  if (fixp->fx_addsy != NULL
      && (!S_IS_DEFINED (fixp->fx_addsy)
	  || S_GET_SEGMENT (fixp->fx_addsy) != sec))
    return 0;

  return (fixp->fx_where + fixp->fx_frag->fr_address) & ~0x1fULL;
}

/* Round up a section size to the appropriate boundary.  */

valueT
md_section_align (segT segment,
		  valueT size)
{
  int align_power = bfd_section_alignment (segment);

  valueT alignment_boundary = (valueT)1 << align_power;

  return (size + alignment_boundary - 1) & ~(alignment_boundary - 1);
}

/* No special undefined symbol handling needed for now.  */

symbolS *
md_undefined_symbol (char *name)
{
  (void)name;
  return NULL;
}

/* Translate internal representation of relocation info to BFD target
   format.  */

arelent *
tc_gen_reloc (asection *section ATTRIBUTE_UNUSED, fixS *fixp)
{
  arelent *reloc;
  asymbol *symbol;
  bfd_reloc_code_real_type r_type;

  if (fixp == NULL)
    {
      /* Cannot use fixp->fx_file, fixp->fx_line here.
         This indicates a severe internal error if fixp itself is NULL.
         A more global error reporting mechanism might be needed,
         or we assume fixp is always valid by design.
         For now, proceed with an internal error message. */
      as_bad (_("Internal error: relocation fixup data (fixp) is NULL"));
      return NULL;
    }

  if (fixp->fx_frag == NULL)
    {
      as_bad_where (fixp->fx_file, fixp->fx_line,
                    _("Internal error: relocation fixup fragment is NULL"));
      return NULL;
    }

  reloc = notes_alloc (sizeof (arelent));
  /* Assuming notes_alloc is robust: it either succeeds or terminates,
     thus no NULL check is performed for notes_alloc itself. */

  reloc->sym_ptr_ptr = notes_alloc (sizeof (asymbol *));
  /* Assuming notes_alloc is robust. */

  symbol = symbol_get_bfdsym (fixp->fx_addsy);
  if (symbol == NULL)
    {
      as_bad_where (fixp->fx_file, fixp->fx_line,
                    _("Cannot find symbol for relocation at 0x%lx"),
                    (unsigned long)(fixp->fx_frag->fr_address + fixp->fx_where));
      return NULL; /* Critical error: cannot form relocation without a symbol. */
    }

  *reloc->sym_ptr_ptr = symbol;
  reloc->address = fixp->fx_frag->fr_address + fixp->fx_where;
  reloc->addend = (tic6x_generate_rela ? fixp->fx_offset : 0);
  r_type = fixp->fx_r_type;
  reloc->howto = bfd_reloc_type_lookup (stdoutput, r_type);

  if (reloc->howto == NULL)
    {
      as_bad_where (fixp->fx_file, fixp->fx_line,
		    _("Cannot represent relocation type %s"),
		    bfd_get_reloc_code_name (r_type));
      return NULL;
    }

  /* Correct for adjustments bfd_install_relocation will make.  */
  if (reloc->howto->pcrel_offset && reloc->howto->partial_inplace)
    {
      reloc->addend += reloc->address;
      /* symbol is guaranteed non-NULL by an earlier check. */
      if (!bfd_is_com_section (bfd_asymbol_section (symbol)))
	reloc->addend -= symbol->value;
    }

  if (r_type == BFD_RELOC_C6000_PCR_H16
      || r_type == BFD_RELOC_C6000_PCR_L16)
    {
      symbolS *t = fixp->tc_fix_data.fix_subsy;
      segT sub_symbol_segment;

      if (t == NULL)
        {
          as_bad_where (fixp->fx_file, fixp->fx_line,
                        _("Internal error: PCR relocation sub-symbol is NULL"));
          return NULL;
        }

      resolve_symbol_value (t);
      sub_symbol_segment = S_GET_SEGMENT (t);

      if (sub_symbol_segment == undefined_section)
	{
          as_bad_where (fixp->fx_file, fixp->fx_line,
		        _("undefined symbol %s in PCR relocation"),
		        S_GET_NAME (t));
          /* This is a critical error: an undefined symbol means the relocation
             cannot be resolved. Returning NULL indicates failure. */
          return NULL;
	}
      else
	{
	  reloc->addend = reloc->address & ~0x1F; /* Mask for alignment. */
	  reloc->addend -= S_GET_VALUE (t);
	}
    }

  return reloc;
}

/* Convert REGNAME to a DWARF-2 register number.  */

enum {
    TIC6X_REG_SIDE_A = 1,
    TIC6X_REG_SIDE_B = 2,

    TIC6X_REG_BANK_SIZE = 16,
    TIC6X_REG_MAX_NUM = 32,

    DW2_OFFSET_A_UPPER_BANK = 37,
    DW2_OFFSET_B_LOWER_BANK = 16,
    DW2_OFFSET_B_UPPER_BANK = 53
};

int
tic6x_regname_to_dw2regnum (char *regname)
{
  tic6x_register reg;
  char *parse_ptr = regname;

  if (!tic6x_parse_register (&parse_ptr, &reg))
    {
      return -1;
    }

  if (reg.num < 0 || reg.num >= TIC6X_REG_MAX_NUM)
    {
      return -1;
    }

  switch (reg.side)
    {
    case TIC6X_REG_SIDE_A:
      if (reg.num < TIC6X_REG_BANK_SIZE)
        {
          return reg.num;
        }
      else
        {
          return (reg.num - TIC6X_REG_BANK_SIZE) + DW2_OFFSET_A_UPPER_BANK;
        }

    case TIC6X_REG_SIDE_B:
      if (reg.num < TIC6X_REG_BANK_SIZE)
        {
          return reg.num + DW2_OFFSET_B_LOWER_BANK;
        }
      else
        {
          return (reg.num - TIC6X_REG_BANK_SIZE) + DW2_OFFSET_B_UPPER_BANK;
        }

    default:
      return -1;
    }
}

/* Initialize the DWARF-2 unwind information for this procedure.  */

#ifndef CFI_REGISTER_B15
#define CFI_REGISTER_B15 31
#endif

#ifndef CFA_OFFSET_ZERO
#define CFA_OFFSET_ZERO 0
#endif

void
tic6x_frame_initial_instructions (void)
{
  cfi_add_CFA_def_cfa (CFI_REGISTER_B15, CFA_OFFSET_ZERO);
}

/* Start an exception table entry.  If idx is nonzero this is an index table
   entry.  */

static void
tic6x_start_unwind_section (const segT text_seg, int idx)
{
  tic6x_unwind_info * const unwind_info = tic6x_get_unwind ();

  const char *section_prefix;
  const char *linkonce_section_prefix;
  int section_type;

  if (idx)
    {
      section_prefix = ELF_STRING_C6000_unwind;
      linkonce_section_prefix = ELF_STRING_C6000_unwind_once;
      section_type = SHT_C6000_UNWIND;
    }
  else
    {
      section_prefix = ELF_STRING_C6000_unwind_info;
      linkonce_section_prefix = ELF_STRING_C6000_unwind_info_once;
      section_type = SHT_PROGBITS;
    }

  const char *seg_name_base = segment_name (text_seg);
  const char *effective_section_name_suffix = seg_name_base;

  if (streq (effective_section_name_suffix, ".text"))
    effective_section_name_suffix = "";

  if (startswith (effective_section_name_suffix, ".gnu.linkonce.t."))
    {
      section_prefix = linkonce_section_prefix;
      effective_section_name_suffix += strlen (".gnu.linkonce.t.");
    }

  const size_t prefix_len = strlen (section_prefix);
  const size_t suffix_len = strlen (effective_section_name_suffix);
  const size_t full_name_len = prefix_len + suffix_len;

  char *section_name = XNEWVEC (char, full_name_len + 1);

  memcpy (section_name, section_prefix, prefix_len);
  memcpy (section_name + prefix_len, effective_section_name_suffix, suffix_len);
  section_name[full_name_len] = '\0';

  int section_flags = SHF_ALLOC;
  int is_linkonce = 0;
  struct elf_section_match match_info = {0};

  if (section_prefix != linkonce_section_prefix && (text_seg->flags & SEC_LINK_ONCE) != 0)
    {
      match_info.group_name = elf_group_name (text_seg);
      if (match_info.group_name == NULL)
	{
	  as_bad (_("group section `%s' has no group signature"),
		  segment_name (text_seg));
	  ignore_rest_of_line ();
	  return;
	}
      section_flags |= SHF_GROUP;
      is_linkonce = 1;
    }

  obj_elf_change_section (section_name, section_type, section_flags, 0, &match_info,
			  is_linkonce);

  if (idx)
    elf_linked_to_section (now_seg) = text_seg;

  seg_info (now_seg)->tc_segment_info_data.text_unwind = unwind_info;
}


static const int
tic6x_unwind_frame_regs[TIC6X_NUM_UNWIND_REGS] =
/* A15 B15 B14 B13 B12 B11 B10  B3 A14 A13 A12 A11 A10.  */
  { 15, 31, 30, 29, 28, 27, 26, 19, 14, 13, 12, 11, 10 };

/* Register save offsets for __c6xabi_push_rts.  */
static const int
tic6x_pop_rts_offset_little[TIC6X_NUM_UNWIND_REGS] =
/* A15 B15 B14 B13 B12 B11 B10  B3 A14 A13 A12 A11 A10.  */
  { -1,  1,  0, -3, -4, -7, -8,-11, -2, -5, -6, -9,-10};

static const int
tic6x_pop_rts_offset_big[TIC6X_NUM_UNWIND_REGS] =
/* A15 B15 B14 B13 B12 B11 B10  B3 A14 A13 A12 A11 A10.  */
  { -2,  1,  0, -4, -3, -8, -7,-12, -1, -6, -5,-10, -9};

/* Map from dwarf register number to unwind frame register number.  */
static int
tic6x_unwind_reg_from_dwarf (int dwarf)
{
  size_t i;

  for (i = 0; i < (size_t)TIC6X_NUM_UNWIND_REGS; i++)
    {
      if (tic6x_unwind_frame_regs[i] == dwarf)
	return (int)i;
    }

  return -1;
}

/* Unwinding bytecode definitions.  */
#define UNWIND_OP_ADD_SP  0x00
#define UNWIND_OP_ADD_SP2 0xd2
#define UNWIND_OP2_POP 0x8000
#define UNWIND_OP2_POP_COMPACT 0xa000
#define UNWIND_OP_POP_REG 0xc0
#define UNWIND_OP_MV_FP 0xd0
#define UNWIND_OP_POP_RTS 0xd1
#define UNWIND_OP_RET 0xe0

/* Maximum stack adjustment for __c6xabi_unwind_cpp_pr3/4 */
#define MAX_COMPACT_SP_OFFSET (0x7f << 3)

static void
tic6x_flush_unwind_word (valueT data)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();
  char *ptr;
  int is_first_entry = 0;

  assert (unwind != NULL);

  /* Create EXTAB entry if it does not exist.  */
  if (unwind->table_entry == NULL)
    {
      tic6x_start_unwind_section (unwind->saved_seg, 0);
      frag_align (2, 0, 0);
      record_alignment (now_seg, 2);
      unwind->table_entry = expr_build_dot ();
      is_first_entry = 1;
    }

  ptr = frag_more (4);

  assert (ptr != NULL);

  if (is_first_entry)
    {
      unwind->frag_start = ptr;
    }

  md_number_to_chars (ptr, data, 4);
}

/* Add a single byte of unwinding data.  */

#include <stdint.h>

#define UNWIND_INITIAL_PERSONALITY              -1
#define UNWIND_PERSONALITY_TYPE_1                1
#define UNWIND_WORD_SIZE_BYTES                   4
#define UNWIND_SPECIAL_FLUSH_BYTE_THRESHOLD      5
#define UNWIND_HEADER_PREFIX                  0x81000000U
#define MASK_LOW_8_BITS                       0xFFU
#define MASK_LOW_16_BITS                      0xFFFFU
#define SHIFT_BITS_PER_BYTE                   8

typedef struct {
  uint32_t data;
  int data_bytes;
  int personality_index;
} tic6x_unwind_info;

tic6x_unwind_info *tic6x_get_unwind(void);
void tic6x_flush_unwind_word(uint32_t word);

static void
tic6x_unwind_byte (int byte_in)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind();

  uint32_t current_byte_val = (uint32_t)(unsigned char)byte_in;

  unwind->data_bytes++;

  if (unwind->data_bytes == UNWIND_SPECIAL_FLUSH_BYTE_THRESHOLD)
    {
      if (unwind->personality_index == UNWIND_INITIAL_PERSONALITY)
	{
	  unwind->personality_index = UNWIND_PERSONALITY_TYPE_1;

	  tic6x_flush_unwind_word(UNWIND_HEADER_PREFIX |
	                          ((unwind->data >> SHIFT_BITS_PER_BYTE) & MASK_LOW_16_BITS));

	  unwind->data = ((unwind->data & MASK_LOW_8_BITS) << SHIFT_BITS_PER_BYTE) | current_byte_val;

	  unwind->data_bytes++;
	}
      else
	{
	  tic6x_flush_unwind_word(unwind->data);

	  unwind->data = current_byte_val;
	}
    }
  else
    {
      unwind->data = (unwind->data << SHIFT_BITS_PER_BYTE) | current_byte_val;

      if ((unwind->data_bytes & (UNWIND_WORD_SIZE_BYTES - 1)) == 0 &&
          unwind->data_bytes > UNWIND_WORD_SIZE_BYTES)
	{
	  tic6x_flush_unwind_word(unwind->data);
	  unwind->data = 0U;
	}
    }
}

/* Add a two-byte unwinding opcode.  */
static void
tic6x_unwind_2byte (unsigned int bytes)
{
  tic6x_unwind_byte (bytes >> 8);
  tic6x_unwind_byte (bytes & 0xff);
}

static void
tic6x_unwind_uleb (offsetT offset)
{
  do
    {
      unsigned char byte = offset & 0x7f;
      offset >>= 7;
      if (offset > 0)
        {
          byte |= 0x80;
        }
      tic6x_unwind_byte (byte);
    }
  while (offset > 0);
}

void
tic6x_cfi_startproc (void)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();

  if (unwind == NULL)
    {
      /*
       * Failed to retrieve unwind information.
       * Cannot proceed with initialization as unwind is required.
       * Since the function has a void return, we simply return.
       * A more robust system might log this error or panic.
       */
      return;
    }

  unwind->personality_index = -1;
  unwind->personality_routine = NULL;

  if (unwind->table_entry)
    as_bad (_("missing .endp before .cfi_startproc"));

  unwind->table_entry = NULL;
  unwind->data_bytes = -1;
}

#define EXIDX_ENTRY_SIZE_BYTES 8
#define EXIDX_WORD_SIZE_BYTES 4
#define PERSONALITY_ROUTINE_COUNT 5

static void
tic6x_output_exidx_entry (void)
{
  char *ptr;
  long entry_address_offset;
  unsigned int marked_pr_dependency_flags;
  segT old_seg;
  subsegT old_subseg;
  tic6x_unwind_info *unwind = tic6x_get_unwind ();

  old_seg = now_seg;
  old_subseg = now_subseg;

  tic6x_start_unwind_section (unwind->saved_seg, 1);
  frag_align (EXIDX_ENTRY_SIZE_BYTES, 0, 0);
  record_alignment (now_seg, EXIDX_ENTRY_SIZE_BYTES);

  ptr = frag_more (EXIDX_ENTRY_SIZE_BYTES);
  memset (ptr, 0, EXIDX_ENTRY_SIZE_BYTES);
  entry_address_offset = frag_now_fix () - EXIDX_ENTRY_SIZE_BYTES;

  fix_new (frag_now, entry_address_offset, EXIDX_WORD_SIZE_BYTES, unwind->function_start, 0, 1,
           BFD_RELOC_C6000_PREL31);

  marked_pr_dependency_flags
    = seg_info (now_seg)->tc_segment_info_data.marked_pr_dependency;

  if (unwind->personality_index >= 0 && unwind->personality_index < PERSONALITY_ROUTINE_COUNT
      && !(marked_pr_dependency_flags & (1 << unwind->personality_index)))
    {
      static const char *const pr_names[PERSONALITY_ROUTINE_COUNT] =
        {
          "__c6xabi_unwind_cpp_pr0",
          "__c6xabi_unwind_cpp_pr1",
          "__c6xabi_unwind_cpp_pr2",
          "__c6xabi_unwind_cpp_pr3",
          "__c6xabi_unwind_cpp_pr4"
        };
      symbolS *pr_symbol = symbol_find_or_make (pr_names[unwind->personality_index]);
      fix_new (frag_now, entry_address_offset, 0, pr_symbol, 0, 1, BFD_RELOC_NONE);
      seg_info (now_seg)->tc_segment_info_data.marked_pr_dependency
        |= (1 << unwind->personality_index);
    }

  if (unwind->table_entry)
    {
      fix_new (frag_now, entry_address_offset + EXIDX_WORD_SIZE_BYTES, EXIDX_WORD_SIZE_BYTES, unwind->table_entry, 0, 1,
               BFD_RELOC_C6000_PREL31);
    }
  else
    {
      md_number_to_chars (ptr + EXIDX_WORD_SIZE_BYTES, unwind->data, EXIDX_WORD_SIZE_BYTES);
    }

  subseg_set (old_seg, old_subseg);
}

static bool
handle_compact_unwinding (tic6x_unwind_info *unwind, offsetT cfa_offset,
                          unsigned safe_mask, unsigned compact_mask,
                          unsigned reg_saved_mask)
{
  if (cfa_offset >= MAX_COMPACT_SP_OFFSET)
    {
      as_bad (_("stack pointer offset too large for personality routine"));
      return false;
    }
  if (reg_saved_mask
      || (unwind->personality_index == 3 && compact_mask != 0)
      || (unwind->personality_index == 4 && safe_mask != 0))
    {
      as_bad (_("stack frame layout does not match personality routine"));
      return false;
    }

  unwind->data = (1u << 31) | (unwind->personality_index << 24);
  if (unwind->cfa_reg == 15)
    unwind->data |= 0x7f << 17;
  else
    unwind->data |= (cfa_offset >> 3) << 17;

  if (unwind->personality_index == 3)
    unwind->data |= safe_mask << 4;
  else
    unwind->data |= compact_mask << 4;
  unwind->data |= unwind->return_reg;
  unwind->data_bytes = 4;
  return true;
}

static void
handle_generic_unwinding_setup (tic6x_unwind_info *unwind)
{
  if (unwind->personality_routine)
    {
      unwind->data = 0;
      unwind->data_bytes = 5;
      tic6x_flush_unwind_word (0);
      long where = frag_now_fix () - 4;
      fix_new (frag_now, where, 4, unwind->personality_routine, 0, 1,
               BFD_RELOC_C6000_PREL31);
    }
  else if (unwind->personality_index > 0)
    {
      unwind->data = 0x8000 | (unwind->personality_index << 8);
      unwind->data_bytes = 2;
    }
  else
    {
      unwind->data = 0x80;
      unwind->data_bytes = 1;
    }
}

static void
emit_return_reg_opcode (tic6x_unwind_info *unwind)
{
  if (unwind->return_reg != UNWIND_B3)
    {
      tic6x_unwind_byte (UNWIND_OP_RET | unwind->return_reg);
    }
}

static void
emit_cfa_offset_opcodes (tic6x_unwind_info *unwind, offsetT cfa_offset)
{
  if (unwind->cfa_reg == 15)
    {
      tic6x_unwind_byte (UNWIND_OP_MV_FP);
    }
  else if (cfa_offset != 0)
    {
      cfa_offset >>= 3;
      if (cfa_offset > 0x80)
        {
          tic6x_unwind_byte (UNWIND_OP_ADD_SP2);
          tic6x_unwind_uleb (cfa_offset - 0x81);
        }
      else if (cfa_offset > 0x40)
        {
          tic6x_unwind_byte (UNWIND_OP_ADD_SP | 0x3f);
          tic6x_unwind_byte (UNWIND_OP_ADD_SP | (cfa_offset - 0x40));
        }
      else
        {
          tic6x_unwind_byte (UNWIND_OP_ADD_SP | (cfa_offset - 1));
        }
    }
}

static void
emit_saved_reg_opcodes (tic6x_unwind_info *unwind, unsigned safe_mask,
                        unsigned compact_mask, unsigned reg_saved_mask)
{
  if (safe_mask)
    {
      tic6x_unwind_2byte (UNWIND_OP2_POP | unwind->safe_mask);
    }
  else if (unwind->pop_rts)
    {
      tic6x_unwind_byte (UNWIND_OP_POP_RTS);
    }
  else if (compact_mask)
    {
      tic6x_unwind_2byte (UNWIND_OP2_POP_COMPACT | unwind->compact_mask);
    }
  else if (reg_saved_mask)
    {
      tic6x_unwind_byte (UNWIND_OP_POP_REG | unwind->saved_reg_count);
      int last_val = 0;
      offsetT cur_offset = 0;
      for (; unwind->saved_reg_count > 0; cur_offset -= 4)
        {
          int val = 0xf;
          for (int reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
            {
              if (!unwind->reg_saved[reg])
                continue;

              if (unwind->reg_offset[reg] == cur_offset)
                {
                  unwind->saved_reg_count--;
                  val = reg;
                  break;
                }
            }
          if ((cur_offset & 4) == 4)
            {
              tic6x_unwind_byte ((last_val << 4) | val);
            }
          else
            {
              last_val = val;
            }
        }
      if ((cur_offset & 4) == 4)
        {
          tic6x_unwind_byte ((last_val << 4) | 0xf);
        }
    }
}

static void
tic6x_output_unwinding (bool need_extab)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();
  unsigned safe_mask = unwind->safe_mask;
  unsigned compact_mask = unwind->compact_mask;
  unsigned reg_saved_mask = unwind->reg_saved_mask;
  offsetT cfa_offset = unwind->cfa_offset;

  if (unwind->personality_index == -2)
    {
      unwind->data = 1;
      tic6x_output_exidx_entry ();
      return;
    }

  if (unwind->personality_index == -1 && unwind->personality_routine == NULL)
    {
      if (reg_saved_mask || cfa_offset >= MAX_COMPACT_SP_OFFSET)
        unwind->personality_index = -1;
      else if (safe_mask)
        unwind->personality_index = 3;
      else
        unwind->personality_index = 4;
    }

  unwind->table_entry = NULL;
  if (unwind->personality_index == 3 || unwind->personality_index == 4)
    {
      if (!handle_compact_unwinding (unwind, cfa_offset, safe_mask,
                                     compact_mask, reg_saved_mask))
        return;
    }
  else
    {
      handle_generic_unwinding_setup (unwind);
      emit_return_reg_opcode (unwind);
      emit_cfa_offset_opcodes (unwind, cfa_offset);
      emit_saved_reg_opcodes (unwind, safe_mask, compact_mask, reg_saved_mask);

      while ((unwind->data_bytes & 3) != 0)
        tic6x_unwind_byte (UNWIND_OP_RET | UNWIND_B3);

      if (unwind->personality_index == -1 && unwind->personality_routine == NULL)
        unwind->personality_index = 0;
    }

  if (need_extab && !unwind->table_entry)
    {
      if (unwind->data_bytes != 4)
        abort ();

      tic6x_flush_unwind_word (unwind->data);
    }
  else if (unwind->table_entry && !need_extab)
    {
      char *ptr = frag_more (4);
      md_number_to_chars (ptr, 0, 4);
    }

  if (unwind->table_entry)
    {
      if (unwind->data_bytes > 0x400)
        as_bad (_("too many unwinding instructions"));

      if (unwind->personality_index == -1)
        {
          valueT tmp = md_chars_to_number (unwind->frag_start + 4, 4);
          tmp |= (valueT) ((unwind->data_bytes - 8) >> 2) << 24;
          md_number_to_chars (unwind->frag_start + 4, tmp, 4);
        }
      else if (unwind->personality_index == 1 || unwind->personality_index == 2)
        {
          valueT tmp = md_chars_to_number (unwind->frag_start, 4);
          tmp |= ((unwind->data_bytes - 4) >> 2) << 16;
          md_number_to_chars (unwind->frag_start, tmp, 4);
        }
    }
  tic6x_output_exidx_entry ();
}

/* FIXME: This will get horribly confused if cfi directives are emitted for
   function epilogue.  */
#include "tic6x_cfi.h"
#include "bpf.h"
#include "as.h"
#include <stdbool.h>
#include <stdlib.h>


static const int CFA_REG_SP = 15;
static const int CFA_REG_B15 = 31;
static const int DWARF_REG_RA_PSEUDO = 19;
static const int DOUBLE_WORD_ALIGNMENT_BYTES = 8;
static const int WORD_SIZE_BYTES = 4;
static const offsetT MAX_UNWIND_OFFSET_NEGATIVE = -0x800;
static const unsigned POP_RTS_REG_MASK = 0x17ff;


static void
initialize_unwind_info(tic6x_unwind_info *unwind)
{
  unwind->cfa_reg = CFA_REG_B15;
  unwind->return_reg = UNWIND_B3;
  unwind->saved_reg_count = 0;
  unwind->pop_rts = false;

  unwind->saved_seg = now_seg;
  unwind->saved_subseg = now_subseg;

  for (int reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
    unwind->reg_saved[reg] = false;
}

static bool
handle_cfi_instruction(tic6x_unwind_info *unwind, const struct cfi_insn_data *insn, offsetT *cfa_offset_ptr)
{
  int reg;
  switch (insn->insn)
    {
    case DW_CFA_advance_loc:
      break;

    case DW_CFA_def_cfa:
      unwind->cfa_reg = insn->u.ri.reg;
      *cfa_offset_ptr = insn->u.ri.offset;
      break;

    case DW_CFA_def_cfa_register:
      unwind->cfa_reg = insn->u.r;
      break;

    case DW_CFA_def_cfa_offset:
      *cfa_offset_ptr = insn->u.i;
      break;

    case DW_CFA_undefined:
    case DW_CFA_same_value:
      reg = tic6x_unwind_reg_from_dwarf (insn->u.r);
      if (reg >= 0)
        unwind->reg_saved[reg] = false;
      break;

    case DW_CFA_offset:
      reg = tic6x_unwind_reg_from_dwarf (insn->u.ri.reg);
      if (reg < 0)
        {
          as_bad (_("unable to generate unwinding opcode for reg %d"),
                  insn->u.ri.reg);
          return false;
        }
      unwind->reg_saved[reg] = true;
      unwind->reg_offset[reg] = insn->u.ri.offset;
      if (insn->u.ri.reg == UNWIND_B3)
        unwind->return_reg = UNWIND_B3;
      break;

    case DW_CFA_register:
      if (insn->u.rr.reg1 != DWARF_REG_RA_PSEUDO)
        {
          as_bad (_("unsupported DWARF register mapping for return address (%d)"),
                  insn->u.rr.reg1);
          return false;
        }

      reg = tic6x_unwind_reg_from_dwarf (insn->u.rr.reg2);
      if (reg < 0)
        {
          as_bad (_("unable to generate unwinding opcode for reg %d"),
                  insn->u.rr.reg2);
          return false;
        }

      unwind->return_reg = reg;
      unwind->reg_saved[UNWIND_B3] = false;
      if (unwind->reg_saved[reg])
        {
          as_bad (_("unable to restore return address from previously restored reg"));
          return false;
        }
      break;

    case DW_CFA_restore:
    case DW_CFA_remember_state:
    case DW_CFA_restore_state:
    case DW_CFA_GNU_window_save:
    case CFI_escape:
    case CFI_val_encoded_addr:
      as_bad (_("unhandled CFA instruction for unwinding (%d)"), insn->insn);
      return false;

    default:
      as_bad (_("unknown CFA instruction encountered (%d)"), insn->insn);
      return false;
    }
  return true;
}

static bool
validate_cfa_register_and_offset(const tic6x_unwind_info *unwind, offsetT cfa_offset)
{
  if (unwind->cfa_reg != CFA_REG_SP && unwind->cfa_reg != CFA_REG_B15)
    {
      as_bad (_("unsupported frame pointer register %d for unwinding"),
              unwind->cfa_reg);
      return false;
    }

  if (unwind->cfa_reg == CFA_REG_SP)
    {
      if (cfa_offset != 0)
        {
          as_bad (_("frame pointer offset must be zero when using SP as CFA"));
          return false;
        }
    }
  else
    {
      if ((cfa_offset % DOUBLE_WORD_ALIGNMENT_BYTES) != 0)
        {
          as_bad (_("unwound stack pointer not doubleword aligned"));
          return false;
        }
    }
  return true;
}

static unsigned
calculate_reg_saved_mask(const tic6x_unwind_info *unwind)
{
  unsigned mask = 0;
  for (int reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
    {
      if (unwind->reg_saved[reg])
        mask |= (1 << (TIC6X_NUM_UNWIND_REGS - (reg + 1)));
    }
  return mask;
}

static bool
check_safe_debug_frame(tic6x_unwind_info *unwind, unsigned *reg_saved_mask_ptr)
{
  if (!*reg_saved_mask_ptr)
    return false;

  offsetT current_save_offset = 0;
  int reg;
  for (reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
    {
      if (!unwind->reg_saved[reg])
        continue;

      if (target_big_endian
          && reg < TIC6X_NUM_UNWIND_REGS - 1
          && unwind->reg_saved[reg + 1]
          && tic6x_unwind_frame_regs[reg] == tic6x_unwind_frame_regs[reg + 1] + 1
          && (tic6x_unwind_frame_regs[reg] & 1) == 1
          && (current_save_offset % DOUBLE_WORD_ALIGNMENT_BYTES) == WORD_SIZE_BYTES)
        {
          if (current_save_offset != unwind->reg_offset[reg + 1]
              || current_save_offset - WORD_SIZE_BYTES != unwind->reg_offset[reg])
            break;
          current_save_offset -= DOUBLE_WORD_ALIGNMENT_BYTES;
          reg++;
        }
      else
        {
          if (current_save_offset != unwind->reg_offset[reg])
            break;
          current_save_offset -= WORD_SIZE_BYTES;
        }
    }

  if (reg == TIC6X_NUM_UNWIND_REGS)
    {
      unwind->safe_mask = *reg_saved_mask_ptr;
      *reg_saved_mask_ptr = 0;
      return true;
    }
  return false;
}

static bool
check_compact_frame(tic6x_unwind_info *unwind, unsigned *reg_saved_mask_ptr)
{
  if (!*reg_saved_mask_ptr)
    return false;

  offsetT current_save_offset = 0;
  int reg;
  for (reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
    {
      if (!unwind->reg_saved[reg])
        continue;

      int reg2 = -1;
      if (reg < TIC6X_NUM_UNWIND_REGS - 1)
        {
          int next_reg = reg + 1;
          if (unwind->reg_saved[next_reg]
              && tic6x_unwind_frame_regs[reg] == tic6x_unwind_frame_regs[next_reg] + 1
              && (tic6x_unwind_frame_regs[next_reg] & 1) == 0
              && current_save_offset != 0)
            {
              reg2 = next_reg;
            }
        }

      if (reg2 >= 0)
        {
          int high_offset_adj = target_big_endian ? WORD_SIZE_BYTES : 0;

          if (current_save_offset + WORD_SIZE_BYTES - high_offset_adj != unwind->reg_offset[reg]
              || current_save_offset + high_offset_adj != unwind->reg_offset[reg2])
            {
              break;
            }
          reg++;
        }
      else
        {
          if (current_save_offset != unwind->reg_offset[reg])
            break;
        }
      current_save_offset -= DOUBLE_WORD_ALIGNMENT_BYTES;
    }

  if (reg == TIC6X_NUM_UNWIND_REGS)
    {
      unwind->compact_mask = *reg_saved_mask_ptr;
      *reg_saved_mask_ptr = 0;
      return true;
    }
  return false;
}

static bool
check_pop_rts_frame(tic6x_unwind_info *unwind, unsigned *reg_saved_mask_ptr)
{
  if (*reg_saved_mask_ptr != POP_RTS_REG_MASK)
    return false;

  const int *pop_rts_offset_table = target_big_endian
                                  ? tic6x_pop_rts_offset_big
                                  : tic6x_pop_rts_offset_little;

  int reg;
  for (reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
    {
      if (reg == UNWIND_B15)
        continue;

      if (unwind->reg_offset[reg] != (offsetT)pop_rts_offset_table[reg] * WORD_SIZE_BYTES)
        break;
    }

  if (reg == TIC6X_NUM_UNWIND_REGS)
    {
      unwind->pop_rts = true;
      *reg_saved_mask_ptr = 0;
      return true;
    }
  return false;
}

static bool
handle_manual_frame_description(tic6x_unwind_info *unwind, unsigned reg_saved_mask, offsetT *save_offset_ptr)
{
  if (!reg_saved_mask)
    {
      *save_offset_ptr = 0;
      return true;
    }

  offsetT min_saved_reg_offset = 0;

  for (int reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
    {
      if (!unwind->reg_saved[reg])
        continue;

      unwind->saved_reg_count++;
      if (unwind->reg_offset[reg] > 0
          || unwind->reg_offset[reg] < MAX_UNWIND_OFFSET_NEGATIVE
          || (unwind->reg_offset[reg] % WORD_SIZE_BYTES) != 0)
        {
          as_bad (_("stack frame layout too complex for unwinder"));
          return false;
        }

      if (unwind->reg_offset[reg] < min_saved_reg_offset)
        min_saved_reg_offset = unwind->reg_offset[reg] - WORD_SIZE_BYTES;
    }

  *save_offset_ptr = min_saved_reg_offset;
  return true;
}


void
tic6x_cfi_endproc (struct fde_entry *fde)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();
  offsetT cfa_offset = 0;
  offsetT save_offset = 0;
  unsigned reg_saved_mask = 0;

  initialize_unwind_info(unwind);

  for (struct cfi_insn_data *insn = fde->data; insn; insn = insn->next)
    {
      if (!handle_cfi_instruction(unwind, insn, &cfa_offset))
        return;
    }

  if (!validate_cfa_register_and_offset(unwind, cfa_offset))
    return;

  reg_saved_mask = calculate_reg_saved_mask(unwind);

  if (check_safe_debug_frame(unwind, &reg_saved_mask)) {
      /* Frame handled by safe debug layout. */
  } else if (check_compact_frame(unwind, &reg_saved_mask)) {
      /* Frame handled by compact layout. */
  } else if (check_pop_rts_frame(unwind, &reg_saved_mask)) {
      /* Frame handled by __c6xabi_pop_rts layout. */
  }

  if (!handle_manual_frame_description(unwind, reg_saved_mask, &save_offset)) {
      return;
  }

  save_offset &= ~(DOUBLE_WORD_ALIGNMENT_BYTES - 1);

  if (unwind->cfa_reg == CFA_REG_B15 && !reg_saved_mask)
    {
      cfa_offset += save_offset;
      if (cfa_offset < 0)
        {
          as_bad (_("unwound frame has negative size"));
          return;
        }
    }

  unwind->reg_saved_mask = reg_saved_mask;
  unwind->cfa_offset = cfa_offset;
  unwind->function_start = fde->start_address;
}
