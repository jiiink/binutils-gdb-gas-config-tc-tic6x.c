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

static tic6x_unwind_info *tic6x_get_unwind(void)
{
    tic6x_unwind_info *unwind = seg_info(now_seg)->tc_segment_info_data.unwind;
    if (unwind)
    {
        return unwind;
    }

    unwind = seg_info(now_seg)->tc_segment_info_data.text_unwind;
    if (unwind)
    {
        return unwind;
    }

    unwind = XNEW(tic6x_unwind_info);
    if (!unwind)
    {
        return NULL;
    }

    memset(unwind, 0, sizeof(*unwind));
    seg_info(now_seg)->tc_segment_info_data.unwind = unwind;

    return unwind;
}

/* Update the selected architecture based on ARCH, giving an error if
   ARCH is an invalid value.  Does not call tic6x_update_features; the
   caller must do that if necessary.  */

static void
tic6x_use_arch (const char *arch)
{
  for (unsigned int i = 0; i < ARRAY_SIZE (tic6x_arches); ++i)
    {
      if (strcmp (arch, tic6x_arches[i].arch) == 0)
        {
          tic6x_arch_enable = tic6x_arches[i].features;
          if (tic6x_seen_insns)
            {
              tic6x_arch_attribute =
                elf32_tic6x_merge_arch_attributes (tic6x_arch_attribute,
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
  for (size_t i = 0; i < ARRAY_SIZE (tic6x_pid_types); i++)
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

#include <stdbool.h>

bool
md_parse_option (int c, const char *arg)
{
  switch (c)
    {
    case OPTION_MARCH:
      tic6x_use_arch (arg);
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
      tic6x_use_pid (arg);
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
      return false;
    }
  return true;
}

static const char * const c6000_option_lines[] =
{
  "  -march=ARCH             enable instructions from architecture ARCH",
  "  -mbig-endian            generate big-endian code",
  "  -mlittle-endian         generate little-endian code",
  "  -mdsbt                  code uses DSBT addressing",
  "  -mno-dsbt               code does not use DSBT addressing",
  "  -mpid=no                code uses position-dependent data addressing",
  "  -mpid=near              code uses position-independent data addressing,\n"
    "                            GOT accesses use near DP addressing",
  "  -mpid=far               code uses position-independent data addressing,\n"
    "                            GOT accesses use far DP addressing",
  "  -mpic                   code addressing is position-independent",
  "  -mno-pic                code addressing is position-dependent"
};

void
md_show_usage (FILE *stream ATTRIBUTE_UNUSED)
{
  if (fputc ('\n', stream) == EOF
      || fprintf (stream, _("TMS320C6000 options:\n")) < 0)
    return;

  for (size_t i = 0; i < ARRAY_SIZE (c6000_option_lines); i++)
    {
      if (fprintf (stream, "%s\n", _(c6000_option_lines[i])) < 0)
        return;
    }

  if (fputc ('\n', stream) == EOF
      || fprintf (stream, _("Supported ARCH values are:")) < 0)
    return;

  for (size_t i = 0; i < ARRAY_SIZE (tic6x_arches); i++)
    {
      if (fprintf (stream, " %s", tic6x_arches[i].arch) < 0)
        return;
    }

  if (fputc ('\n', stream) == EOF)
    return;
}

/* Update enabled features based on the current architecture and
   related settings.  */
static void
tic6x_update_features (void)
{
  const unsigned int arch = tic6x_arch_enable;
  const bool is_c64x = (arch & TIC6X_INSN_C64X) != 0;
  const bool is_c64xp = (arch & TIC6X_INSN_C64XP) != 0;
  const bool has_extended_regs = (arch & (TIC6X_INSN_C64X | TIC6X_INSN_C67XP)) != 0;

  tic6x_features = arch;
  tic6x_num_registers = has_extended_regs ? 32 : 16;
  tic6x_predicate_a0 = is_c64x;
  tic6x_can_cross_fp_boundary = has_extended_regs;
  tic6x_long_data_constraints = !is_c64x;
  tic6x_compact_insns = is_c64xp;
}

/* Do configuration after all options have been parsed.  */

void tic6x_after_parse_args(void)
{
    if (tic6x_update_features() != 0)
    {
        fprintf(stderr, "Fatal error: Failed to update tic6x features.\n");
        exit(EXIT_FAILURE);
    }
}

/* Parse a .cantunwind directive.  */
static void
s_tic6x_cantunwind (int ignored ATTRIBUTE_UNUSED)
{
  const int UNWIND_STATE_EMPTY = 0;
  const int UNWIND_STATE_FNSTART_SEEN = -1;
  const int PERSONALITY_INDEX_UNSET = -1;
  const int PERSONALITY_INDEX_CANTUNWIND = -2;

  tic6x_unwind_info *unwind = tic6x_get_unwind ();
  if (!unwind)
    {
      as_fatal (_("internal error: failed to get unwind info"));
      return;
    }

  if (unwind->data_bytes == UNWIND_STATE_EMPTY)
    {
      return;
    }

  if (unwind->data_bytes != UNWIND_STATE_FNSTART_SEEN)
    {
      as_bad (_("unexpected .cantunwind directive"));
      return;
    }

  demand_empty_rest_of_line ();

  const int personality_is_set =
    unwind->personality_routine
    || (unwind->personality_index != PERSONALITY_INDEX_UNSET);

  if (personality_is_set)
    {
      as_bad (_("personality routine specified for cantunwind frame"));
    }

  unwind->personality_index = PERSONALITY_INDEX_CANTUNWIND;
}

/* Parse a .handlerdata directive.  */
static bool
s_is_duplicate_handlerdata (const tic6x_unwind_info *unwind)
{
  const int handler_data_already_specified = -2;
  return unwind->table_entry || unwind->personality_index == handler_data_already_specified;
}

static bool
s_is_personality_routine_missing (const tic6x_unwind_info *unwind)
{
  const int personality_not_specified = -1;
  return unwind->personality_index == personality_not_specified
         && unwind->personality_routine == NULL;
}

static void
s_tic6x_handlerdata (int ignored ATTRIBUTE_UNUSED)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();

  if (!unwind->saved_seg)
    {
      as_bad (_("unexpected .handlerdata directive"));
      return;
    }

  if (s_is_duplicate_handlerdata (unwind))
    {
      as_bad (_("duplicate .handlerdata directive"));
      return;
    }

  if (s_is_personality_routine_missing (unwind))
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

  if (!unwind)
    {
      return;
    }

  if (unwind->data_bytes != 0)
    {
      if (!unwind->table_entry)
        {
          tic6x_output_unwinding (false);
        }
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
  const int MAX_PERSONALITY_INDEX = 15;
  tic6x_unwind_info *unwind = tic6x_get_unwind ();

  if (unwind->personality_routine || unwind->personality_index != -1)
    {
      as_bad (_("duplicate .personalityindex directive"));
      return;
    }

  expressionS exp;
  expression (&exp);

  if (exp.X_op != O_constant
      || (unsigned int) exp.X_add_number > MAX_PERSONALITY_INDEX)
    {
      as_bad (_("bad personality routine number"));
      ignore_rest_of_line ();
      return;
    }

  unwind->personality_index = exp.X_add_number;
  demand_empty_rest_of_line ();
}

static void
s_tic6x_personality (int ignored ATTRIBUTE_UNUSED)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();

  if (unwind == NULL)
    {
      as_fatal (_("internal error: failed to get unwind info for .personality"));
      return;
    }

  if (unwind->personality_routine != NULL || unwind->personality_index != -1)
    {
      as_bad (_("duplicate .personality directive"));
      return;
    }

  char *name;
  char c = get_symbol_name (&name);

  unwind->personality_routine = symbol_find_or_make (name);
  (void) restore_line_pointer (c);
  demand_empty_rest_of_line ();
}

/* Parse a .arch directive.  */
static void
s_tic6x_arch (int ignored ATTRIBUTE_UNUSED)
{
  const char *start = input_line_pointer;
  const char *end = start;

  while (*end != '\0'
	 && !is_end_of_stmt (*end)
	 && !is_whitespace (*end))
    {
      end++;
    }

  size_t len = end - start;
  char *arch = malloc (len + 1);

  if (arch == NULL)
    {
      return;
    }

  memcpy (arch, start, len);
  arch[len] = '\0';

  tic6x_use_arch (arch);
  free (arch);

  tic6x_update_features ();
  input_line_pointer = (char *) end;
  demand_empty_rest_of_line ();
}

/* Parse a .ehtype directive.  */

static void
s_tic6x_ehtype (int ignored ATTRIBUTE_UNUSED)
{
  static const int EHTYPE_RELOC_SIZE = 4;
  expressionS exp;

#ifdef md_flush_pending_output
  md_flush_pending_output ();
#endif

  if (is_it_end_of_statement ())
    {
      demand_empty_rest_of_line ();
      return;
    }

#ifdef md_cons_align
  md_cons_align (EHTYPE_RELOC_SIZE);
#endif

  expression (&exp);

  if (exp.X_op != O_symbol)
    {
      as_bad (_("expected symbol"));
      return;
    }

  char *p = frag_more (EHTYPE_RELOC_SIZE);
  memset (p, 0, EHTYPE_RELOC_SIZE);
  fix_new_exp (frag_now, p - frag_now->fr_literal, EHTYPE_RELOC_SIZE,
	       &exp, 0, BFD_RELOC_C6000_EHTYPE);

  demand_empty_rest_of_line ();
}

/* Parse a .nocmp directive.  */

static void
s_tic6x_nocmp (int ignored ATTRIBUTE_UNUSED)
{
  seg_info_type *current_seg_info = seg_info (now_seg);

  if (current_seg_info)
    {
      current_seg_info->tc_segment_info_data.nocmp = true;
      demand_empty_rest_of_line ();
    }
}

/* .scomm pseudo-op handler.

   This is a new pseudo-op to handle putting objects in .scommon.
   By doing this the linker won't need to do any work,
   and more importantly it removes the implicit -G arg necessary to
   correctly link the object file.  */

static void
define_local_scomm_symbol (symbolS *symbolP, offsetT size, int align2)
{
  segT old_sec = now_seg;
  int old_subsec = now_subseg;
  char *pfrag;

  record_alignment (sbss_section, align2);
  subseg_set (sbss_section, 0);

  if (align2 > 0)
    {
      frag_align (align2, 0, 0);
    }

  if (S_GET_SEGMENT (symbolP) == sbss_section)
    {
      symbol_get_frag (symbolP)->fr_symbol = NULL;
    }

  symbol_set_frag (symbolP, frag_now);

  pfrag = frag_var (rs_org, 1, 1, 0, symbolP, size, NULL);
  *pfrag = 0;
  S_SET_SIZE (symbolP, size);
  S_SET_SEGMENT (symbolP, sbss_section);
  S_CLEAR_EXTERNAL (symbolP);
  subseg_set (old_sec, old_subsec);
}

static void
define_global_scomm_symbol (symbolS *symbolP, offsetT size, int align2)
{
  S_SET_VALUE (symbolP, size);
  S_SET_ALIGN (symbolP, 1 << align2);
  S_SET_EXTERNAL (symbolP);
  S_SET_SEGMENT (symbolP, &scom_section);
}

static bool
validate_scomm_symbol (symbolS *symbolP, offsetT size)
{
  if (S_IS_DEFINED (symbolP))
    {
      as_bad (_("attempt to re-define symbol `%s'"), S_GET_NAME (symbolP));
      ignore_rest_of_line ();
      return false;
    }

  if (S_GET_VALUE (symbolP) != 0 && S_GET_VALUE (symbolP) != (valueT) size)
    {
      as_bad (_("attempt to redefine `%s' with a different length"),
	      S_GET_NAME (symbolP));
      ignore_rest_of_line ();
      return false;
    }

  return true;
}

static bool
get_alignment_power (int *align2_p)
{
  offsetT align = 8;
  if (*input_line_pointer == ',')
    {
      ++input_line_pointer;
      align = get_absolute_expression ();
      if (align <= 0)
	{
	  as_warn (_("alignment is not a positive number"));
	  align = 8;
	}
    }

  if (align == 0)
    {
      *align2_p = 0;
      return true;
    }

  offsetT temp_align = align;
  int align2 = 0;
  while ((temp_align & 1) == 0)
    {
      temp_align >>= 1;
      align2++;
    }

  if (temp_align != 1)
    {
      as_bad (_("alignment is not a power of 2"));
      ignore_rest_of_line ();
      return false;
    }

  *align2_p = align2;
  return true;
}

static bool
parse_scomm_operands (offsetT *size_p, int *align2_p)
{
  SKIP_WHITESPACE ();
  if (*input_line_pointer != ',')
    {
      as_bad (_("expected comma after symbol name"));
      ignore_rest_of_line ();
      return false;
    }
  input_line_pointer++;

  *size_p = get_absolute_expression ();
  if (*size_p < 0)
    {
      as_warn (_("invalid length for .scomm directive"));
      ignore_rest_of_line ();
      return false;
    }

  return get_alignment_power (align2_p);
}

static void
s_tic6x_scomm (int ignore ATTRIBUTE_UNUSED)
{
  char *name;
  char c;
  char *p;
  offsetT size;
  int align2;
  symbolS *symbolP;

  c = get_symbol_name (&name);

  p = input_line_pointer;
  (void) restore_line_pointer (c);

  if (!parse_scomm_operands (&size, &align2))
    {
      return;
    }

  *p = 0;
  symbolP = symbol_find_or_make (name);
  *p = c;

  if (!validate_scomm_symbol (symbolP, size))
    {
      return;
    }

  if (symbol_get_obj (symbolP)->local)
    {
      define_local_scomm_symbol (symbolP, size, align2);
    }
  else
    {
      define_global_scomm_symbol (symbolP, size, align2);
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
  const int tag = obj_elf_vendor_attribute (OBJ_ATTR_PROC);

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

  for (size_t i = 0; i < ARRAY_SIZE (tic6x_attributes); i++)
  {
    if (tic6x_attributes[i].name != NULL && strcmp(name, tic6x_attributes[i].name) == 0)
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

static void
initialize_opcode_hash (void)
{
  opcode_hash = str_htab_create ();
  for (tic6x_opcode_id id = 0; id < tic6x_opcode_max; id++)
    {
      tic6x_opcode_list *opc = XNEW (tic6x_opcode_list);
      opc->id = id;
      opc->next = str_hash_find (opcode_hash, tic6x_opcode_table[id].name);
      str_hash_insert (opcode_hash, tic6x_opcode_table[id].name, opc, 1);
    }
}

static void
create_sbss_section (void)
{
  segT seg = now_seg;
  subsegT subseg = now_subseg;

  sbss_section = subseg_new (".bss", 0);
  seg_info (sbss_section)->bss = 1;

  flagword applicable = bfd_applicable_section_flags (stdoutput);
  bfd_set_section_flags (sbss_section, applicable & SEC_ALLOC);

  subseg_set (seg, subseg);
}

static void
create_scommon_section (void)
{
  scom_section = *bfd_com_section_ptr;
  scom_section.name = ".scommon";
  scom_section.output_section = &scom_section;
  scom_section.symbol = &scom_symbol;

  scom_symbol = *bfd_com_section_ptr->symbol;
  scom_symbol.name = ".scommon";
  scom_symbol.section = &scom_section;
}

void
md_begin (void)
{
  bfd_set_arch_mach (stdoutput, TARGET_ARCH, 0);

  initialize_opcode_hash ();
  create_sbss_section ();
  create_scommon_section ();
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

static void
report_bad_predicate (const char *start, const char *end)
{
  char bad_predicate_str[32];
  size_t len = end - start;

  if (len >= sizeof (bad_predicate_str))
    len = sizeof (bad_predicate_str) - 1;

  strncpy (bad_predicate_str, start, len);
  bad_predicate_str[len] = '\0';
  as_bad (_("bad predicate '%s'"), bad_predicate_str);
}

static void
set_creg_from_predicate (bool areg, char reg_num_char)
{
  switch (reg_num_char)
    {
    case '0':
      tic6x_line_creg = areg ? 6 : 1;
      if (areg && !tic6x_predicate_a0)
	as_bad (_("predication on A0 not supported on this architecture"));
      break;
    case '1':
      tic6x_line_creg = areg ? 4 : 2;
      break;
    case '2':
      tic6x_line_creg = areg ? 5 : 3;
      break;
    }
}

static int
handle_predicate (void)
{
  char *p = input_line_pointer;
  const char * const start_of_predicate = p - 1;
  char *end_bracket = p;

  while (*end_bracket != ']' && !is_end_of_stmt (*end_bracket))
    end_bracket++;

  if (*end_bracket != ']')
    return 0;

  const char * const endp = end_bracket + 1;

  if (tic6x_line_creg)
    as_bad (_("multiple predicates on same line"));

  bool z = false;
  if (*p == '!')
    {
      z = true;
      p++;
    }

  bool areg;
  if (*p == 'A' || *p == 'a')
    areg = true;
  else if (*p == 'B' || *p == 'b')
    areg = false;
  else
    {
      report_bad_predicate (start_of_predicate, endp);
      input_line_pointer = (char *) endp;
      return 1;
    }
  p++;

  char reg_num_char = *p;
  if ((reg_num_char < '0' || reg_num_char > '2') || p[1] != ']')
    {
      report_bad_predicate (start_of_predicate, endp);
      input_line_pointer = (char *) endp;
      return 1;
    }

  input_line_pointer = p + 2;
  tic6x_line_z = z;
  set_creg_from_predicate (areg, reg_num_char);

  return 1;
}

static int
handle_parallel_specifier (void)
{
  if (input_line_pointer[0] != '|')
    return 0;

  if (input_line_pointer[1] == '^')
    {
      tic6x_line_spmask = true;
      input_line_pointer += 2;
    }
  else
    {
      input_line_pointer += 1;
    }

  if (tic6x_line_parallel)
    as_bad (_("multiple '||' on same line"));
  tic6x_line_parallel = true;

  if (tic6x_line_creg)
    as_bad (_("'||' after predicate"));

  return 1;
}

int
tic6x_unrecognized_line (int c)
{
  switch (c)
    {
    case '|':
      return handle_parallel_specifier ();
    case '[':
      return handle_predicate ();
    default:
      return 0;
    }
}

/* Do any target-specific handling of a label required.  */

void
tic6x_frob_label (symbolS *sym)
{
  if (tic6x_line_parallel)
    {
      as_bad (_("label after '||'"));
      tic6x_line_parallel = false;
      tic6x_line_spmask = false;
    }

  if (tic6x_line_creg)
    {
      as_bad (_("label after predicate"));
      tic6x_line_creg = 0;
      tic6x_line_z = 0;
    }

  segment_info_type *si = seg_info (now_seg);
  if (!si)
    {
      as_bad (_("Internal error: could not retrieve segment info"));
      return;
    }

  tic6x_segment_info *tc_info = &si->tc_segment_info_data;
  tic6x_label_list *new_node = XNEW (tic6x_label_list);

  new_node->label = sym;
  new_node->next = tc_info->label_list;
  tc_info->label_list = new_node;

  /* Defining tc_frob_label overrides the ELF definition of
     obj_frob_label, so we need to apply its effects here.  */
  dwarf2_emit_label (sym);
}

/* At end-of-line, give errors for start-of-line decorations that
   needed an instruction but were not followed by one.  */

static void
check_and_reset_parallel_state (void)
{
  if (tic6x_line_parallel)
    {
      as_bad (_("'||' not followed by instruction"));
      tic6x_line_parallel = false;
      tic6x_line_spmask = false;
    }
}

static void
check_and_reset_predicate_state (void)
{
  if (tic6x_line_creg)
    {
      as_bad (_("predicate not followed by instruction"));
      tic6x_line_creg = 0;
      tic6x_line_z = 0;
    }
}

static void
tic6x_end_of_line (void)
{
  check_and_reset_parallel_state ();
  check_and_reset_predicate_state ();
}

/* Do any target-specific handling of the start of a logical line.  */

extern void tic6x_end_of_line(void);

void tic6x_start_line_hook(void) __attribute__((alias("tic6x_end_of_line")));

/* Do target-specific handling immediately after an input file from
   the command line, and any other inputs it includes, have been
   read.  */

void tic6x_cleanup(void)
{
    (void)tic6x_end_of_line();
}

/* Do target-specific initialization after arguments have been
   processed and the output file created.  */

void tic6x_init_after_args(void)
{
    elf32_tic6x_set_use_rela_p(stdoutput, tic6x_generate_rela);
}

/* Free LIST of labels (possibly NULL).  */

static void
tic6x_free_label_list (tic6x_label_list *list)
{
  tic6x_label_list *current = list;
  while (current != NULL)
    {
      tic6x_label_list *next = current->next;
      free (current);
      current = next;
    }
}

/* Handle a data alignment of N bytes.  */

void
tic6x_cons_align (int n)
{
  (void) n;

  segment_info_type *seginfo = seg_info (now_seg);

  if (!seginfo)
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
tic6x_do_align (int n, char *fill, int len ATTRIBUTE_UNUSED, int max)
{
  if (n <= 0
      || n > 5
      || max < 0
      || max >= (1 << n)
      || need_pass_2
      || fill != NULL
      || !subseg_text_p (now_seg))
    {
      return false;
    }

  if (frag_now_fix () != 0)
    {
      if (frag_now->fr_type != rs_machine_dependent)
        {
          frag_wane (frag_now);
        }
      frag_new (0);
    }

  frag_grow (32);
  fragS *align_frag = frag_now;
  char *p = frag_var (rs_machine_dependent, 32, 32, max, NULL, n, NULL);

  if (p != align_frag->fr_literal)
    {
      abort ();
    }

  align_frag->tc_frag_data.is_insns = false;
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
  char *r = *p;

  switch (tolower ((unsigned char) *r))
    {
    case 'a':
      reg->side = 1;
      break;
    case 'b':
      reg->side = 2;
      break;
    default:
      return false;
    }
  r++;

  if (!isdigit ((unsigned char) *r))
    {
      return false;
    }

  int num = *r - '0';
  r++;

  if (isdigit ((unsigned char) *r))
    {
      if (num == 0)
        {
          return false;
        }
      num = num * 10 + (*r - '0');
      r++;
    }

  if (isdigit ((unsigned char) *r))
    {
      return false;
    }

  if (num >= 32)
    {
      return false;
    }

  reg->num = num;
  *p = r;
  return true;
}

/* Parse the initial two characters of a functional unit name starting
   at *P.  If OK, set *BASE and *SIDE and return true; otherwise,
   return FALSE.  */

static bool
tic6x_parse_func_unit_base (char *p, tic6x_func_unit_base *base,
			    unsigned int *side)
{
  if (!p || !base || !side || p[0] == '\0' || p[1] == '\0')
    {
      return false;
    }

  tic6x_func_unit_base parsed_base;
  switch (tolower ((unsigned char) p[0]))
    {
    case 'd':
      parsed_base = tic6x_func_unit_d;
      break;
    case 'l':
      parsed_base = tic6x_func_unit_l;
      break;
    case 'm':
      parsed_base = tic6x_func_unit_m;
      break;
    case 's':
      parsed_base = tic6x_func_unit_s;
      break;
    default:
      return false;
    }

  unsigned int parsed_side;
  switch (p[1])
    {
    case '1':
      parsed_side = 1;
      break;
    case '2':
      parsed_side = 2;
      break;
    default:
      return false;
    }

  *base = parsed_base;
  *side = parsed_side;
  return true;
}

/* Parse an operand starting at *P.  If the operand parses OK, return
   TRUE and store the value in *OP; otherwise return FALSE (possibly
   changing *OP).  In any case, update *P to point to the following
   comma or end of line.  The possible operand forms are given by
   OP_FORMS.  For diagnostics, this is operand OPNO of an opcode
   starting at STR, length OPC_LEN.  */

static bool
parse_keyword (char **p, const char *keyword, tic6x_operand_form form,
	       tic6x_operand *op)
{
  size_t len = strlen (keyword);
  if (strncasecmp (*p, keyword, len) == 0)
    {
      char *rq = *p + len;
      skip_whitespace (rq);
      if (is_end_of_stmt (*rq) || *rq == ',')
	{
	  op->form = form;
	  *p = rq;
	  return true;
	}
    }
  return false;
}

static bool
try_parse_func_unit (char **p, tic6x_operand *op, unsigned int op_forms)
{
  if (!(op_forms & TIC6X_OP_FUNC_UNIT))
    return false;

  tic6x_func_unit_base base = tic6x_func_unit_nfu;
  unsigned int side = 0;

  if (tic6x_parse_func_unit_base (*p, &base, &side))
    {
      char *rq = *p + 2;
      skip_whitespace (rq);
      if (is_end_of_stmt (*rq) || *rq == ',')
	{
	  op->form = TIC6X_OP_FUNC_UNIT;
	  op->value.func_unit.base = base;
	  op->value.func_unit.side = side;
	  *p = rq;
	  return true;
	}
    }
  return false;
}

static bool
try_parse_ctrl_reg (char **p, tic6x_operand *op, unsigned int op_forms)
{
  if (!(op_forms & TIC6X_OP_CTRL))
    return false;

  for (tic6x_ctrl_id crid = 0; crid < tic6x_ctrl_max; crid++)
    {
      const char *name = tic6x_ctrl_table[crid].name;
      size_t len = strlen (name);

      if (strncasecmp (name, *p, len) == 0)
	{
	  char *rq = *p + len;
	  skip_whitespace (rq);
	  if (is_end_of_stmt (*rq) || *rq == ',')
	    {
	      op->form = TIC6X_OP_CTRL;
	      op->value.ctrl = crid;
	      if (!(tic6x_ctrl_table[crid].isa_variants & tic6x_features))
		as_bad (_("control register '%s' not supported "
			  "on this architecture"),
			name);
	      *p = rq;
	      return true;
	    }
	}
    }
  return false;
}

static char *
parse_mem_offset (char *q, tic6x_mem *mem, unsigned int op_forms)
{
  char endc;
  switch (*q)
    {
    case '[':
      mem->scaled = tic6x_offset_scaled;
      endc = ']';
      q++;
      break;
    case '(':
      mem->scaled = tic6x_offset_unscaled;
      endc = ')';
      q++;
      break;
    default:
      return NULL;
    }
  skip_whitespace (q);

  if (mem->scaled == tic6x_offset_scaled || (op_forms & TIC6X_OP_MEM_UNREG))
    {
      char *rq = q;
      tic6x_register offset_reg;
      if (tic6x_parse_register (&rq, &offset_reg))
	{
	  skip_whitespace (rq);
	  if (*rq == endc)
	    {
	      mem->offset_is_reg = true;
	      mem->offset.reg = offset_reg;
	      if (offset_reg.num >= tic6x_num_registers)
		as_bad (_("register number %u not supported on this architecture"),
			offset_reg.num);
	      return rq + 1;
	    }
	}
    }

  char *save_input_line_pointer = input_line_pointer;
  input_line_pointer = q;
  expression (&mem->offset.exp);
  q = input_line_pointer;
  input_line_pointer = save_input_line_pointer;
  skip_whitespace (q);

  if (*q != endc)
    return NULL;

  mem->offset_is_reg = false;
  return q + 1;
}

static bool
try_parse_mem_ref (char **p, tic6x_operand *op, unsigned int op_forms)
{
  if (!(op_forms & (TIC6X_OP_MEM_NOUNREG | TIC6X_OP_MEM_UNREG)))
    return false;

  char *q = *p;
  if (*q != '*')
    return false;

  q++;
  skip_whitespace (q);

  tic6x_mem_mod mem_mod = tic6x_mem_mod_none;
  if (*q == '+')
    {
      mem_mod = (q[1] == '+') ? tic6x_mem_mod_preinc : tic6x_mem_mod_plus;
      q += (mem_mod == tic6x_mem_mod_preinc) ? 2 : 1;
    }
  else if (*q == '-')
    {
      mem_mod = (q[1] == '-') ? tic6x_mem_mod_predec : tic6x_mem_mod_minus;
      q += (mem_mod == tic6x_mem_mod_predec) ? 2 : 1;
    }
  skip_whitespace (q);

  tic6x_register base_reg;
  if (!tic6x_parse_register (&q, &base_reg))
    return false;
  if (base_reg.num >= tic6x_num_registers)
    as_bad (_("register number %u not supported on this architecture"),
	    base_reg.num);
  skip_whitespace (q);

  if (mem_mod == tic6x_mem_mod_none)
    {
      if (q[0] == '+' && q[1] == '+')
	{
	  mem_mod = tic6x_mem_mod_postinc;
	  q += 2;
	}
      else if (q[0] == '-' && q[1] == '-')
	{
	  mem_mod = tic6x_mem_mod_postdec;
	  q += 2;
	}
    }

  bool offset_parsed = false;
  if (mem_mod != tic6x_mem_mod_none)
    {
      char *next_p = parse_mem_offset (q, &op->value.mem, op_forms);
      if (next_p)
	{
	  q = next_p;
	  offset_parsed = true;
	}
    }

  if ((mem_mod == tic6x_mem_mod_plus || mem_mod == tic6x_mem_mod_minus)
      && !offset_parsed)
    return false;

  if (!offset_parsed)
    {
      op->value.mem.scaled = tic6x_offset_none;
      op->value.mem.offset_is_reg = false;
    }

  skip_whitespace (q);
  if (!is_end_of_stmt (*q) && *q != ',')
    return false;

  op->form = op_forms & (TIC6X_OP_MEM_NOUNREG | TIC6X_OP_MEM_UNREG);
  op->value.mem.base_reg = base_reg;
  op->value.mem.mod = mem_mod;
  *p = q;
  return true;
}

static bool
try_parse_reg_or_regpair (char **p, tic6x_operand *op, unsigned int op_forms,
			  char *str, int opc_len, unsigned int opno)
{
  if (!(op_forms & (TIC6X_OP_REG | TIC6X_OP_REGPAIR)))
    return false;

  char *q = *p;
  tic6x_register first_reg;
  if (!tic6x_parse_register (&q, &first_reg))
    return false;

  if (*q == ':' && (op_forms & TIC6X_OP_REGPAIR))
    {
      char *rq = q + 1;
      tic6x_register second_reg;
      if (tic6x_parse_register (&rq, &second_reg))
	{
	  skip_whitespace (rq);
	  if (is_end_of_stmt (*rq) || *rq == ',')
	    {
	      if ((second_reg.num & 1)
		  || (first_reg.num != second_reg.num + 1)
		  || (first_reg.side != second_reg.side))
		as_bad (_("register pair for operand %u of '%.*s' "
			  " not a valid even/odd pair"), opno, opc_len, str);
	      op->form = TIC6X_OP_REGPAIR;
	      op->value.reg = second_reg;
	      *p = rq;
	      if (first_reg.num >= tic6x_num_registers)
		as_bad (_("register number %u not supported on this architecture"),
			first_reg.num);
	      if (second_reg.num >= tic6x_num_registers)
		as_bad (_("register number %u not supported on this architecture"),
			second_reg.num);
	      return true;
	    }
	}
    }

  if (op_forms & TIC6X_OP_REG)
    {
      skip_whitespace (q);
      if (is_end_of_stmt (*q) || *q == ',')
	{
	  op->form = TIC6X_OP_REG;
	  op->value.reg = first_reg;
	  *p = q;
	  if (first_reg.num >= tic6x_num_registers)
	    as_bad (_("register number %u not supported on this architecture"),
		    first_reg.num);
	  return true;
	}
    }

  return false;
}

static bool
try_parse_expression (char **p, tic6x_operand *op, unsigned int op_forms)
{
  if (!(op_forms & TIC6X_OP_EXP))
    return false;

  char *save_input_line_pointer = input_line_pointer;
  input_line_pointer = *p;
  op->form = TIC6X_OP_EXP;
  expression (&op->value.exp);
  *p = input_line_pointer;
  input_line_pointer = save_input_line_pointer;
  return true;
}

static bool
tic6x_parse_operand (char **p, tic6x_operand *op, unsigned int op_forms,
		     char *str, int opc_len, unsigned int opno)
{
  bool operand_parsed = false;
  char *q = *p;

  if ((op_forms & (TIC6X_OP_MEM_NOUNREG | TIC6X_OP_MEM_UNREG))
      == (TIC6X_OP_MEM_NOUNREG | TIC6X_OP_MEM_UNREG))
    abort ();

  if (!operand_parsed)
    operand_parsed = try_parse_func_unit (&q, op, op_forms);
  if (!operand_parsed && (op_forms & TIC6X_OP_IRP))
    operand_parsed = parse_keyword (&q, "irp", TIC6X_OP_IRP, op);
  if (!operand_parsed && (op_forms & TIC6X_OP_NRP))
    operand_parsed = parse_keyword (&q, "nrp", TIC6X_OP_NRP, op);
  if (!operand_parsed)
    operand_parsed = try_parse_ctrl_reg (&q, op, op_forms);
  if (!operand_parsed)
    operand_parsed = try_parse_mem_ref (&q, op, op_forms);
  if (!operand_parsed)
    operand_parsed = try_parse_reg_or_regpair (&q, op, op_forms, str, opc_len, opno);
  if (!operand_parsed)
    operand_parsed = try_parse_expression (&q, op, op_forms);

  if (operand_parsed)
    {
      skip_whitespace (q);
      if (!is_end_of_stmt (*q) && *q != ',')
	{
	  operand_parsed = false;
	  as_bad (_("junk after operand %u of '%.*s'"), opno, opc_len, str);
	  while (!is_end_of_stmt (*q) && *q != ',')
	    q++;
	}
    }

  if (!operand_parsed)
    {
      switch (op_forms)
	{
	case TIC6X_OP_REG | TIC6X_OP_REGPAIR:
	  as_bad (_("bad register or register pair for operand %u of '%.*s'"),
		  opno, opc_len, str);
	  break;
	case TIC6X_OP_REG | TIC6X_OP_CTRL:
	case TIC6X_OP_REG:
	  as_bad (_("bad register for operand %u of '%.*s'"),
		  opno, opc_len, str);
	  break;
	case TIC6X_OP_REGPAIR:
	  as_bad (_("bad register pair for operand %u of '%.*s'"),
		  opno, opc_len, str);
	  break;
	case TIC6X_OP_FUNC_UNIT:
	  as_bad (_("bad functional unit for operand %u of '%.*s'"),
		  opno, opc_len, str);
	  break;
	default:
	  as_bad (_("bad operand %u of '%.*s'"), opno, opc_len, str);
	  break;
	}
      while (!is_end_of_stmt (*q) && *q != ',')
	q++;
    }

  *p = q;
  return operand_parsed;
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

static operatorT
find_tic6x_operator (const char *name)
{
  if (*name != '$')
    return O_illegal;

  for (unsigned int i = 0; i < ARRAY_SIZE (tic6x_operators); i++)
    if (strcasecmp (name + 1, tic6x_operators[i].name) == 0)
      return tic6x_operators[i].op;

  return O_illegal;
}

static int
consume_char (const char **stream, char c)
{
  const char *p = *stream;
  skip_whitespace (p);
  if (*p != c)
    return 0;
  *stream = p + 1;
  return 1;
}

static int
parse_identifier (const char **stream, const char **start, const char **end)
{
  const char *p = *stream;
  skip_whitespace (p);

  if (!is_name_beginner (*p))
    return 0;

  *start = p;
  do
    {
      p++;
    }
  while (is_part_of_name (*p));
  *end = p;
  *stream = p;
  return 1;
}

static symbolS *
make_symbol_from_slice (const char *start, const char *end)
{
  char c = *end;
  symbolS *sym;

  *(char *) end = '\0';
  sym = symbol_find_or_make (start);
  *(char *) end = c;

  return sym;
}

static int
parse_operator_args (const char **stream, operatorT op, expressionS *exprP)
{
  const char *name_start, *name_end;
  symbolS *sym, *op_sym = NULL;
  const char *p = *stream;

  if (!consume_char (&p, '('))
    return 0;

  if (!parse_identifier (&p, &name_start, &name_end))
    return 0;

  if (op == O_pcr_offset)
    {
      const char *op_name_start, *op_name_end;
      if (!consume_char (&p, ','))
	return 0;
      if (!parse_identifier (&p, &op_name_start, &op_name_end))
	return 0;
      op_sym = make_symbol_from_slice (op_name_start, op_name_end);
    }

  if (!consume_char (&p, ')'))
    return 0;

  {
    char c = *name_end;
    const char *inner_name = name_start;
    *(char *) name_end = '\0';

    if (op == O_dsbt_index && strcmp (inner_name, "__c6xabi_DSBT_BASE") != 0)
      {
	as_bad (_("$DSBT_INDEX must be used with __c6xabi_DSBT_BASE"));
	inner_name = "__c6xabi_DSBT_BASE";
      }
    sym = symbol_find_or_make (inner_name);
    *(char *) name_end = c;
  }

  exprP->X_op = op;
  exprP->X_add_symbol = sym;
  exprP->X_add_number = 0;
  exprP->X_op_symbol = op_sym;
  exprP->X_md = 0;

  *stream = p;
  return 1;
}

int
tic6x_parse_name (const char *name, expressionS *exprP,
		  enum expr_mode mode ATTRIBUTE_UNUSED, char *nextchar)
{
  operatorT op = find_tic6x_operator (name);
  if (op == O_illegal)
    return 0;

  const char *p = input_line_pointer;
  *input_line_pointer = *nextchar;

  if (parse_operator_args (&p, op, exprP))
    {
      input_line_pointer = (char *) p;
      *nextchar = *input_line_pointer;
      *input_line_pointer = '\0';
      return 1;
    }
  else
    {
      *input_line_pointer = '\0';
      return 0;
    }
}

/* Create a fixup for an expression.  Same arguments as fix_new_exp,
   plus FIX_ADDA which is TRUE for ADDA instructions (to indicate that
   fixes resolving to constants should have those constants implicitly
   shifted) and FALSE otherwise, but look for C6X-specific expression
   types and adjust the relocations or give errors accordingly.  */

static void
tic6x_fix_new_exp (fragS *frag, int where, int size, expressionS *exp,
		   int pcrel, bfd_reloc_code_real_type r_type,
		   bool fix_adda)
{
  bfd_reloc_code_real_type new_reloc = BFD_RELOC_UNUSED;
  symbolS *subsy = NULL;
  const char *unsupported_op_name = NULL;
  fixS *fix;

  switch (exp->X_op)
    {
    case O_dsbt_index:
      switch (r_type)
	{
	case BFD_RELOC_C6000_SBR_U15_W:
	  new_reloc = BFD_RELOC_C6000_DSBT_INDEX;
	  break;
	default:
	  unsupported_op_name = "$DSBT_INDEX";
	  break;
	}
      break;

    case O_got:
      switch (r_type)
	{
	case BFD_RELOC_C6000_SBR_U15_W:
	  new_reloc = BFD_RELOC_C6000_SBR_GOT_U15_W;
	  break;
	default:
	  unsupported_op_name = "$GOT";
	  break;
	}
      break;

    case O_dpr_got:
      switch (r_type)
	{
	case BFD_RELOC_C6000_ABS_L16:
	  new_reloc = BFD_RELOC_C6000_SBR_GOT_L16_W;
	  break;
	case BFD_RELOC_C6000_ABS_H16:
	  new_reloc = BFD_RELOC_C6000_SBR_GOT_H16_W;
	  break;
	default:
	  unsupported_op_name = "$DPR_GOT";
	  break;
	}
      break;

    case O_dpr_byte:
      switch (r_type)
	{
	case BFD_RELOC_C6000_ABS_S16:
	  new_reloc = BFD_RELOC_C6000_SBR_S16;
	  break;
	case BFD_RELOC_C6000_ABS_L16:
	  new_reloc = BFD_RELOC_C6000_SBR_L16_B;
	  break;
	case BFD_RELOC_C6000_ABS_H16:
	  new_reloc = BFD_RELOC_C6000_SBR_H16_B;
	  break;
	default:
	  unsupported_op_name = "$DPR_BYTE";
	  break;
	}
      break;

    case O_dpr_hword:
      switch (r_type)
	{
	case BFD_RELOC_C6000_ABS_L16:
	  new_reloc = BFD_RELOC_C6000_SBR_L16_H;
	  break;
	case BFD_RELOC_C6000_ABS_H16:
	  new_reloc = BFD_RELOC_C6000_SBR_H16_H;
	  break;
	default:
	  unsupported_op_name = "$DPR_HWORD";
	  break;
	}
      break;

    case O_dpr_word:
      switch (r_type)
	{
	case BFD_RELOC_C6000_ABS_L16:
	  new_reloc = BFD_RELOC_C6000_SBR_L16_W;
	  break;
	case BFD_RELOC_C6000_ABS_H16:
	  new_reloc = BFD_RELOC_C6000_SBR_H16_W;
	  break;
	default:
	  unsupported_op_name = "$DPR_WORD";
	  break;
	}
      break;

    case O_pcr_offset:
      subsy = exp->X_op_symbol;
      switch (r_type)
	{
	case BFD_RELOC_C6000_ABS_S16:
	case BFD_RELOC_C6000_ABS_L16:
	  new_reloc = BFD_RELOC_C6000_PCR_L16;
	  break;
	case BFD_RELOC_C6000_ABS_H16:
	  new_reloc = BFD_RELOC_C6000_PCR_H16;
	  break;
	default:
	  unsupported_op_name = "$PCR_OFFSET";
	  subsy = NULL;
	  break;
	}
      break;

    case O_symbol:
      break;

    default:
      if (pcrel)
	{
	  as_bad (_("invalid PC-relative operand"));
	  return;
	}
      break;
    }

  if (unsupported_op_name)
    {
      as_bad (_("%s not supported in this context"), unsupported_op_name);
      return;
    }

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
  bfd_reloc_code_real_type r_type;

  switch (size)
    {
    case 1:
      r_type = BFD_RELOC_8;
      break;

    case 2:
      r_type = BFD_RELOC_16;
      break;

    case 4:
      r_type = BFD_RELOC_32;
      break;

    default:
      as_bad (_("no %d-byte relocations available"), size);
      return;
    }

  tic6x_fix_new_exp (frag, where, size, exp, 0, r_type, false);
}

/* Initialize target-specific fix data.  */

void tic6x_init_fix_data(fixS *fixP)
{
    if (fixP)
    {
        memset(&fixP->tc_fix_data, 0, sizeof(fixP->tc_fix_data));
    }
}

/* Return true if the fix can be handled by GAS, false if it must
   be passed through to the linker.  */

bool
tic6x_fix_adjustable (fixS *fixP)
{
  switch (fixP->fx_r_type)
    {
      /* Adjust_reloc_syms doesn't know about the GOT.  */
    case BFD_RELOC_C6000_SBR_GOT_U15_W:
    case BFD_RELOC_C6000_SBR_GOT_H16_W:
    case BFD_RELOC_C6000_SBR_GOT_L16_W:
    case BFD_RELOC_C6000_EHTYPE:
    case BFD_RELOC_C6000_PREL31:
    case BFD_RELOC_C6000_PCR_H16:
    case BFD_RELOC_C6000_PCR_L16:
      return 0;

    default:
      return 1;
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
      abort ();
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
match_side_register (const tic6x_operand *op, unsigned int expected_side)
{
  return (op->value.reg.side == expected_side)
	   ? tic6x_match_matches
	   : tic6x_match_wrong_side;
}

static tic6x_operand_match
match_areg (const tic6x_operand *op, unsigned int cross)
{
  if (op->value.reg.side != cross)
    return tic6x_match_wrong_side;

  if (op->value.reg.side == 2
      && (op->value.reg.num == 14 || op->value.reg.num == 15))
    return tic6x_match_matches;

  return tic6x_match_bad_address;
}

static tic6x_operand_match
match_retreg (const tic6x_operand *op, unsigned int side)
{
  if (op->value.reg.side != side)
    return tic6x_match_wrong_side;

  return (op->value.reg.num == 3)
	   ? tic6x_match_matches
	   : tic6x_match_bad_return;
}

static tic6x_operand_match
match_ctrl (const tic6x_operand *op, tic6x_rw rw)
{
  const unsigned int ctrl_rw = tic6x_ctrl_table[op->value.ctrl].rw;
  switch (rw)
    {
    case tic6x_rw_read:
      if (ctrl_rw == tic6x_rw_read || ctrl_rw == tic6x_rw_read_write)
	return tic6x_match_matches;
      return tic6x_match_ctrl_write_only;

    case tic6x_rw_write:
      if (ctrl_rw == tic6x_rw_write || ctrl_rw == tic6x_rw_read_write)
	return tic6x_match_matches;
      return tic6x_match_ctrl_read_only;

    default:
      abort ();
    }
}

static tic6x_operand_match
match_mem_deref (const tic6x_operand *op, unsigned int side)
{
  if (op->value.mem.mod != tic6x_mem_mod_none)
    return tic6x_match_bad_mem;

  if (op->value.mem.scaled != tic6x_offset_none)
    abort ();

  if (op->value.mem.base_reg.side != side)
    return tic6x_match_bad_mem;

  return tic6x_match_matches;
}

static tic6x_operand_match
match_mem_short_ndw (const tic6x_operand *op, tic6x_operand_form form,
		     unsigned int side)
{
  const struct tic6x_mem_operand *mem = &op->value.mem;

  if (mem->base_reg.side != side)
    return tic6x_match_bad_mem;

  if (mem->mod == tic6x_mem_mod_none)
    {
      if (mem->scaled != tic6x_offset_none)
	abort ();
      return tic6x_match_matches;
    }

  if (mem->scaled == tic6x_offset_none)
    {
      if (mem->mod == tic6x_mem_mod_plus || mem->mod == tic6x_mem_mod_minus)
	abort ();
      return tic6x_match_matches;
    }

  if (mem->offset_is_reg)
    {
      if (mem->scaled == tic6x_offset_unscaled
	  && form != tic6x_operand_mem_ndw)
	abort ();

      return (mem->offset.reg.side == side)
	       ? tic6x_match_matches
	       : tic6x_match_bad_mem;
    }

  return (mem->offset.exp.X_op == O_constant)
	   ? tic6x_match_matches
	   : tic6x_match_bad_mem;
}

static tic6x_operand_match
match_mem_long (const tic6x_operand *op)
{
  const struct tic6x_mem_operand *mem = &op->value.mem;

  if (mem->base_reg.side != 2
      || (mem->base_reg.num != 14 && mem->base_reg.num != 15))
    return tic6x_match_bad_mem;

  switch (mem->mod)
    {
    case tic6x_mem_mod_none:
      if (mem->scaled != tic6x_offset_none)
	abort ();
      return tic6x_match_matches;

    case tic6x_mem_mod_plus:
      if (mem->scaled == tic6x_offset_none)
	abort ();
      if (mem->offset_is_reg)
	return tic6x_match_bad_mem;
      if (mem->scaled == tic6x_offset_scaled
	  && mem->offset.exp.X_op != O_constant)
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
}

static tic6x_operand_match
tic6x_operand_matches_form (const tic6x_operand *op, tic6x_operand_form form,
			    tic6x_rw rw, unsigned int side, unsigned int cross,
			    unsigned int data_side)
{
  if (tic6x_coarse_operand_form (form) != op->form)
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
      return match_side_register (op, side);

    case tic6x_operand_xreg:
    case tic6x_operand_xregpair:
      return match_side_register (op, cross);

    case tic6x_operand_dreg:
    case tic6x_operand_dregpair:
      return match_side_register (op, data_side);

    case tic6x_operand_areg:
      return match_areg (op, cross);

    case tic6x_operand_retreg:
      return match_retreg (op, side);

    case tic6x_operand_ctrl:
      return match_ctrl (op, rw);

    case tic6x_operand_mem_deref:
      return match_mem_deref (op, side);

    case tic6x_operand_mem_short:
    case tic6x_operand_mem_ndw:
      return match_mem_short_ndw (op, form, side);

    case tic6x_operand_mem_long:
      return match_mem_long (op);

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
    }
  abort ();
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
    }
  abort ();
}

/* Given a memory reference *MEM_REF as originally parsed, fill in
   defaults for missing offsets.  */

static void
set_mem_ref_offset_to_constant (tic6x_mem_ref *mem_ref, long value)
{
  mem_ref->offset_is_reg = false;
  memset (&mem_ref->offset.exp, 0, sizeof (mem_ref->offset.exp));
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
        {
          abort ();
        }
      mem_ref->mod = tic6x_mem_mod_plus;
      mem_ref->scaled = tic6x_offset_unscaled;
      set_mem_ref_offset_to_constant (mem_ref, 0);
      break;

    case tic6x_mem_mod_plus:
    case tic6x_mem_mod_minus:
      if (mem_ref->scaled == tic6x_offset_none)
        {
          abort ();
        }
      break;

    case tic6x_mem_mod_preinc:
    case tic6x_mem_mod_predec:
    case tic6x_mem_mod_postinc:
    case tic6x_mem_mod_postdec:
      if (mem_ref->scaled == tic6x_offset_none)
        {
          mem_ref->scaled = tic6x_offset_scaled;
          set_mem_ref_offset_to_constant (mem_ref, 1);
        }
      break;

    default:
      abort ();
    }
}

/* Return the encoding in the 8-bit field of an SPMASK or SPMASKR
   instruction of the specified UNIT, side SIDE.  */

static unsigned int
tic6x_encode_spmask (tic6x_func_unit_base unit, unsigned int side)
{
  static const int offsets[] = { -1, 1, 3, 5 };
  const unsigned int num_units = sizeof (offsets) / sizeof (offsets[0]);

  if ((unsigned int) unit >= num_units)
    {
      abort ();
    }

  return 1U << (side + offsets[unit]);
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

static unsigned int
fail_with_error (bool print_errors, const char *message, unsigned int opno,
		 int opc_len, const char *str, bool *ok)
{
  if (print_errors)
    as_bad (message, opno + 1, opc_len, str);
  *ok = false;
  return 0;
}

static unsigned int
fail_with_divisibility_error (bool print_errors, unsigned int opno,
			      int opc_len, const char *str,
			      unsigned int divisor, bool *ok)
{
  if (print_errors)
    as_bad (_("offset in operand %u of '%.*s' not divisible by %u"),
	    opno + 1, opc_len, str, divisor);
  *ok = false;
  return 0;
}

static bool
encode_unsigned_constant (offsetT number, unsigned int width, unsigned int *value)
{
  if (number < 0 || number >= (1LL << width))
    return false;
  *value = (unsigned int) number;
  return true;
}

static bool
encode_signed_constant (offsetT number, unsigned int width, unsigned int *value)
{
  offsetT min_val = -(1LL << (width - 1));
  offsetT max_val = (1LL << (width - 1)) - 1;
  if (number < min_val || number > max_val)
    return false;
  *value = (unsigned int) number & ((1U << width) - 1);
  return true;
}

static void
setup_fixup (expressionS *exp, int pcrel, bfd_reloc_code_real_type r_type,
	     bool adda, expressionS **fix_exp, int *fix_pcrel,
	     bfd_reloc_code_real_type *fx_r_type, bool *fix_adda,
	     bool *fix_needed)
{
  *fix_needed = true;
  *fix_exp = exp;
  *fix_pcrel = pcrel;
  *fx_r_type = r_type;
  *fix_adda = adda;
}

static bfd_reloc_code_real_type
get_pcrel_reloc_type (const tic6x_insn_field *fldd)
{
  unsigned int pos = fldd->bitfields[0].low_pos;
  unsigned int width = fldd->bitfields[0].width;

  if (pos == 7 && width == 21)
    return BFD_RELOC_C6000_PCR_S21;
  if (pos == 16 && width == 12)
    return BFD_RELOC_C6000_PCR_S12;
  if (pos == 13 && width == 10)
    return BFD_RELOC_C6000_PCR_S10;
  if (pos == 16 && width == 7)
    return BFD_RELOC_C6000_PCR_S7;

  return BFD_RELOC_UNUSED;
}

static unsigned int
get_fcyc_bits_for_sploop (int sploop_ii)
{
  if (sploop_ii <= 1) return 0;
  if (sploop_ii <= 2) return 1;
  if (sploop_ii <= 4) return 2;
  if (sploop_ii <= 8) return 3;
  if (sploop_ii <= 14) return 4;
  abort ();
}

static unsigned int
reverse_bits (unsigned int value, unsigned int num_bits)
{
  unsigned int result = 0;
  for (unsigned int i = 0; i < num_bits; ++i)
    {
      result = (result << 1) | (value & 1);
      value >>= 1;
    }
  return result;
}

static unsigned int
encode_mem_mod (tic6x_mem_mod mod)
{
  switch (mod)
    {
    case tic6x_mem_mod_plus: return 1;
    case tic6x_mem_mod_minus: return 0;
    case tic6x_mem_mod_preinc: return 9;
    case tic6x_mem_mod_predec: return 8;
    case tic6x_mem_mod_postinc: return 11;
    case tic6x_mem_mod_postdec: return 10;
    default: abort ();
    }
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
  const tic6x_opcode *opct = &tic6x_opcode_table[id];
  const tic6x_insn_format *fmt = &tic6x_insn_format_table[opct->format];
  unsigned int opcode_value = fmt->cst_bits;

  for (unsigned int fld = 0; fld < opct->num_fixed_fields; fld++)
    {
      if (opct->fixed_fields[fld].min_val == opct->fixed_fields[fld].max_val)
	{
	  const tic6x_insn_field *fldd
	    = tic6x_field_from_fmt (fmt, opct->fixed_fields[fld].field_id);
	  if (fldd == NULL)
	    abort ();
	  opcode_value |= opct->fixed_fields[fld].min_val << fldd->bitfields[0].low_pos;
	}
    }

  for (unsigned int fld = 0; fld < opct->num_variable_fields; fld++)
    {
      const tic6x_variable_field_coding *var_field = &opct->variable_fields[fld];
      const tic6x_insn_field *fldd = tic6x_field_from_fmt (fmt, var_field->field_id);
      if (fldd == NULL)
	abort ();

      unsigned int opno = var_field->operand_num;
      unsigned int value = 0;
      tic6x_mem_ref mem;

      switch (var_field->coding_method)
	{
	case tic6x_coding_ucst:
	  if (operands[opno].form != TIC6X_OP_EXP || operands[opno].value.exp.X_op != O_constant)
	    abort ();
	  if (!encode_unsigned_constant (operands[opno].value.exp.X_add_number,
					 fldd->bitfields[0].width, &value))
	    return fail_with_error (print_errors, _("operand %u of '%.*s' out of range"),
				     opno, opc_len, str, ok);
	  break;

	case tic6x_coding_scst:
	  if (operands[opno].form != TIC6X_OP_EXP)
	    abort ();
	  if (operands[opno].value.exp.X_op == O_constant)
	    {
	      if (!encode_signed_constant (SEXT (operands[opno].value.exp.X_add_number),
					   fldd->bitfields[0].width, &value))
		return fail_with_error (print_errors, _("operand %u of '%.*s' out of range"),
					 opno, opc_len, str, ok);
	    }
	  else
	    {
	      if (fldd->bitfields[0].low_pos != 7 || fldd->bitfields[0].width != 16)
		abort ();
	      setup_fixup (&operands[opno].value.exp, 0, BFD_RELOC_C6000_ABS_S16, false,
			   fix_exp, fix_pcrel, fx_r_type, fix_adda, fix_needed);
	    }
	  break;

	case tic6x_coding_ucst_minus_one:
	  if (operands[opno].form != TIC6X_OP_EXP || operands[opno].value.exp.X_op != O_constant)
	    abort ();
	  if (!encode_unsigned_constant (operands[opno].value.exp.X_add_number - 1,
					 fldd->bitfields[0].width, &value))
	    return fail_with_error (print_errors, _("operand %u of '%.*s' out of range"),
				     opno, opc_len, str, ok);
	  break;

	case tic6x_coding_scst_negate:
	  if (operands[opno].form != TIC6X_OP_EXP || operands[opno].value.exp.X_op != O_constant)
	    abort ();
	  if (!encode_signed_constant (SEXT (-operands[opno].value.exp.X_add_number),
				       fldd->bitfields[0].width, &value))
	    return fail_with_error (print_errors, _("operand %u of '%.*s' out of range"),
				     opno, opc_len, str, ok);
	  break;

	case tic6x_coding_ulcst_dpr_byte:
	case tic6x_coding_ulcst_dpr_half:
	case tic6x_coding_ulcst_dpr_word:
	  {
	    unsigned int bits = tic6x_dpr_shift (var_field->coding_method);
	    expressionS *expp;
	    bool adda_flag;
	    bool is_const = false;
	    expressionS const_exp;

	    if (operands[opno].form == TIC6X_OP_EXP)
	      {
		expp = &operands[opno].value.exp;
		adda_flag = true;
	      }
	    else if (operands[opno].form == TIC6X_OP_MEM_NOUNREG)
	      {
		mem = operands[opno].value.mem;
		tic6x_default_mem_ref (&mem);
		if (mem.offset_is_reg || mem.scaled != tic6x_offset_unscaled || mem.mod == tic6x_mem_mod_none)
		  abort ();
		expp = &mem.offset.exp;
		adda_flag = false;
	      }
	    else
	      abort ();

	    if (expp->X_op == O_constant)
	      {
		is_const = true;
		const_exp = *expp;
		if (operands[opno].form == TIC6X_OP_MEM_NOUNREG)
		  {
		    if (const_exp.X_add_number & ((1u << bits) - 1))
		      return fail_with_divisibility_error (print_errors, opno, opc_len, str, 1u << bits, ok);
		    const_exp.X_add_number >>= bits;
		  }
	      }

	    if (is_const)
	      {
		if (!encode_unsigned_constant (const_exp.X_add_number, fldd->bitfields[0].width, &value))
		  return fail_with_error (print_errors, _("operand %u of '%.*s' out of range"), opno, opc_len, str, ok);
	      }
	    else
	      {
		if (fldd->bitfields[0].low_pos != 8 || fldd->bitfields[0].width != 15)
		  abort ();
		setup_fixup (expp, 0, tic6x_dpr_reloc (var_field->coding_method), adda_flag,
			     fix_exp, fix_pcrel, fx_r_type, fix_adda, fix_needed);
	      }
	  }
	  break;

	case tic6x_coding_lcst_low16:
	case tic6x_coding_lcst_high16:
	  if (operands[opno].form != TIC6X_OP_EXP)
	    abort ();
	  if (operands[opno].value.exp.X_op == O_constant)
	    {
	      offsetT num = operands[opno].value.exp.X_add_number;
	      value = (var_field->coding_method == tic6x_coding_lcst_low16)
		      ? (num & 0xffff) : ((num >> 16) & 0xffff);
	    }
	  else
	    {
	      if (fldd->bitfields[0].low_pos != 7 || fldd->bitfields[0].width != 16)
		abort ();
	      bfd_reloc_code_real_type r_type = (var_field->coding_method == tic6x_coding_lcst_low16)
		? BFD_RELOC_C6000_ABS_L16 : BFD_RELOC_C6000_ABS_H16;
	      setup_fixup (&operands[opno].value.exp, 0, r_type, false,
			   fix_exp, fix_pcrel, fx_r_type, fix_adda, fix_needed);
	    }
	  break;

	case tic6x_coding_pcrel:
	case tic6x_coding_pcrel_half:
	  {
	    if (operands[opno].form != TIC6X_OP_EXP)
	      abort ();
	    bfd_reloc_code_real_type r_type = get_pcrel_reloc_type (fldd);
	    if (r_type == BFD_RELOC_UNUSED)
	      abort ();
	    setup_fixup (&operands[opno].value.exp, 1, r_type, false,
			 fix_exp, fix_pcrel, fx_r_type, fix_adda, fix_needed);
	  }
	  break;

	case tic6x_coding_regpair_lsb:
	  if (operands[opno].form == TIC6X_OP_REGPAIR)
	    value = operands[opno].value.reg.num;
	  else
	    abort ();
	  break;

	case tic6x_coding_regpair_msb:
	  if (operands[opno].form == TIC6X_OP_REGPAIR)
	    value = operands[opno].value.reg.num + 1;
	  else
	    abort ();
	  break;

	case tic6x_coding_reg:
	  if (operands[opno].form == TIC6X_OP_REG || operands[opno].form == TIC6X_OP_REGPAIR)
	    value = operands[opno].value.reg.num;
	  else if (operands[opno].form == TIC6X_OP_MEM_NOUNREG || operands[opno].form == TIC6X_OP_MEM_UNREG)
	    value = operands[opno].value.mem.base_reg.num;
	  else
	    abort ();
	  break;

	case tic6x_coding_areg:
	  if (operands[opno].form == TIC6X_OP_REG)
	    value = (operands[opno].value.reg.num == 15);
	  else if (operands[opno].form == TIC6X_OP_MEM_NOUNREG)
	    value = (operands[opno].value.mem.base_reg.num == 15);
	  else
	    abort ();
	  break;

	case tic6x_coding_crlo:
	  if (operands[opno].form != TIC6X_OP_CTRL)
	    abort ();
	  value = tic6x_ctrl_table[operands[opno].value.ctrl].crlo;
	  break;

	case tic6x_coding_crhi:
	  if (operands[opno].form != TIC6X_OP_CTRL)
	    abort ();
	  value = 0;
	  break;

	case tic6x_coding_reg_shift:
	  if (operands[opno].form != TIC6X_OP_REGPAIR)
	    abort ();
	  value = operands[opno].value.reg.num >> 1;
	  break;

	case tic6x_coding_mem_offset:
	  if (operands[opno].form != TIC6X_OP_MEM_NOUNREG)
	    abort ();
	  mem = operands[opno].value.mem;
	  tic6x_default_mem_ref (&mem);
	  if (mem.offset_is_reg)
	    {
	      if (mem.scaled != tic6x_offset_scaled)
		abort ();
	      value = mem.offset.reg.num;
	    }
	  else
	    {
	      if (mem.offset.exp.X_op != O_constant)
		abort ();
	      unsigned int scale = (mem.scaled == tic6x_offset_scaled) ? 1 : opct->operand_info[opno].size;
	      if (scale != 1 && scale != 2 && scale != 4 && scale != 8)
		abort ();
	      offsetT offset = mem.offset.exp.X_add_number;
	      if (offset < 0 || offset >= (1LL << fldd->bitfields[0].width) * scale)
		return fail_with_error (print_errors, _("offset in operand %u of '%.*s' out of range"),
					 opno, opc_len, str, ok);
	      if (offset % scale != 0)
		return fail_with_divisibility_error (print_errors, opno, opc_len, str, scale, ok);
	      value = offset / scale;
	    }
	  break;

	case tic6x_coding_mem_offset_noscale:
	  if (operands[opno].form != TIC6X_OP_MEM_UNREG)
	    abort ();
	  mem = operands[opno].value.mem;
	  tic6x_default_mem_ref (&mem);
	  if (mem.offset_is_reg)
	    value = mem.offset.reg.num;
	  else
	    {
	      if (mem.offset.exp.X_op != O_constant)
		abort ();
	      if (!encode_unsigned_constant (mem.offset.exp.X_add_number, fldd->bitfields[0].width, &value))
		return fail_with_error (print_errors, _("offset in operand %u of '%.*s' out of range"),
					 opno, opc_len, str, ok);
	    }
	  break;

	case tic6x_coding_mem_mode:
	  if (operands[opno].form != TIC6X_OP_MEM_NOUNREG && operands[opno].form != TIC6X_OP_MEM_UNREG)
	    abort ();
	  mem = operands[opno].value.mem;
	  tic6x_default_mem_ref (&mem);
	  value = encode_mem_mod (mem.mod);
	  if (mem.offset_is_reg)
	    value += 4;
	  break;

	case tic6x_coding_scaled:
	  if (operands[opno].form != TIC6X_OP_MEM_UNREG)
	    abort ();
	  mem = operands[opno].value.mem;
	  tic6x_default_mem_ref (&mem);
	  value = (mem.scaled == tic6x_offset_scaled);
	  break;

	case tic6x_coding_spmask:
	  if (fldd->bitfields[0].low_pos != 18)
	    abort ();
	  for (unsigned int i = 0; i < num_operands; i++)
	    {
	      unsigned int v = tic6x_encode_spmask (operands[i].value.func_unit.base,
						    operands[i].value.func_unit.side);
	      if (value & v)
		return fail_with_error (print_errors, _("functional unit already masked for operand %u of '%.*s'"),
					 i, opc_len, str, ok);
	      value |= v;
	    }
	  break;

	case tic6x_coding_reg_unused:
	  value = 0;
	  break;

	case tic6x_coding_fstg:
	case tic6x_coding_fcyc:
	  if (operands[opno].form != TIC6X_OP_EXP || operands[opno].value.exp.X_op != O_constant)
	    abort ();
	  if (!sploop_ii)
	    return fail_with_error (print_errors, _("'%.*s' instruction not in a software pipelined loop"),
				     0, opc_len, str, ok);

	  unsigned int fcyc_bits = get_fcyc_bits_for_sploop (sploop_ii);
	  if (fcyc_bits > fldd->bitfields[0].width)
	    abort ();

	  offsetT number = operands[opno].value.exp.X_add_number;
	  if (var_field->coding_method == tic6x_coding_fstg)
	    {
	      unsigned int stage_bits = fldd->bitfields[0].width - fcyc_bits;
	      if (!encode_unsigned_constant (number, stage_bits, &value))
		return fail_with_error (print_errors, _("operand %u of '%.*s' out of range"), opno, opc_len, str, ok);
	      value = reverse_bits (value, stage_bits) << fcyc_bits;
	    }
	  else /* tic6x_coding_fcyc */
	    {
	      if (number < 0 || number >= sploop_ii)
		return fail_with_error (print_errors, _("operand %u of '%.*s' out of range"), opno, opc_len, str, ok);
	      value = number;
	    }
	  break;

	case tic6x_coding_fu:
	  value = (func_unit_side == 2);
	  break;

	case tic6x_coding_data_fu:
	  value = (func_unit_data_side == 2);
	  break;

	case tic6x_coding_xpath:
	  value = func_unit_cross;
	  break;

	default:
	  abort ();
	}

      for (unsigned int ffld = 0; ffld < opct->num_fixed_fields; ffld++)
	if (opct->fixed_fields[ffld].field_id == var_field->field_id
	    && (value < opct->fixed_fields[ffld].min_val
		|| value > opct->fixed_fields[ffld].max_val))
	  return fail_with_error (print_errors, _("operand %u of '%.*s' out of range"),
				   opno, opc_len, str, ok);

      opcode_value |= value << fldd->bitfields[0].low_pos;
    }

  if (this_line_creg)
    {
      const tic6x_insn_field *creg = tic6x_field_from_fmt (fmt, tic6x_field_creg);
      if (creg == NULL)
	return fail_with_error (print_errors, _("instruction '%.*s' cannot be predicated"),
				 0, opc_len, str, ok);

      const tic6x_insn_field *z = tic6x_field_from_fmt (fmt, tic6x_field_z);
      if (z == NULL)
	abort ();

      opcode_value |= this_line_creg << creg->bitfields[0].low_pos;
      opcode_value |= this_line_z << z->bitfields[0].low_pos;
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
  const unsigned char *p = (const unsigned char *)buf;
  int step = 1;
  int i;

  if (!target_big_endian)
    {
      p += n - 1;
      step = -1;
    }

  for (i = 0; i < n; i++)
    {
      result <<= 8;
      result |= *p;
      p += step;
    }

  return result;
}

/* Assemble the instruction starting at STR (an opcode, with the
   opcode name all-lowercase).  */

static void
initialize_assembly (char **p_ptr, const char *str, int *opc_len)
{
  char *p = *p_ptr;
  while (!is_end_of_stmt (*p) && !is_whitespace (*p))
    p++;

  if (p == str)
    abort ();

  *opc_len = p - str;
  *p_ptr = p;

  tic6x_seen_insns = true;
  if (tic6x_arch_attribute == C6XABI_Tag_ISA_none)
    tic6x_arch_attribute = C6XABI_Tag_ISA_C674X;
}

static bool
parse_functional_unit (char **p_ptr, tic6x_func_unit_base *base,
		       unsigned int *side, unsigned int *cross,
		       unsigned int *cross_side, unsigned int *data_side)
{
  char *p = *p_ptr;
  skip_whitespace (p);
  if (*p != '.')
    return true;

  tic6x_func_unit_base maybe_base = tic6x_func_unit_nfu;
  unsigned int maybe_side = 0;
  unsigned int maybe_cross = 0;
  unsigned int maybe_data_side = 0;

  if (!tic6x_parse_func_unit_base (p + 1, &maybe_base, &maybe_side))
    return true;

  if (is_whitespace (p[3]) || is_end_of_stmt (p[3]))
    p += 3;
  else if ((p[3] == 'x' || p[3] == 'X')
	   && (is_whitespace (p[4]) || is_end_of_stmt (p[4])))
    {
      maybe_cross = 1;
      p += 4;
    }
  else if (maybe_base == tic6x_func_unit_d && (p[3] == 't' || p[3] == 'T')
	   && (p[4] == '1' || p[4] == '2')
	   && (is_whitespace (p[5]) || is_end_of_stmt (p[5])))
    {
      maybe_data_side = p[4] - '0';
      p += 5;
    }
  else
    return true;

  *base = maybe_base;
  *side = maybe_side;
  *cross = maybe_cross;
  *cross_side = (maybe_cross ? 3 - maybe_side : maybe_side);
  *data_side = maybe_data_side;
  *p_ptr = p;
  skip_whitespace (*p_ptr);
  return true;
}

static bool
is_opcode_fu_compatible (const tic6x_opcode * op,
			 tic6x_func_unit_base func_unit_base,
			 unsigned int func_unit_side,
			 unsigned int func_unit_cross,
			 unsigned int func_unit_data_side)
{
  if (op->func_unit != func_unit_base)
    return false;
  if (func_unit_side == 1 && (op->flags & TIC6X_FLAG_SIDE_B_ONLY))
    return false;
  if (func_unit_cross && (op->flags & TIC6X_FLAG_NO_CROSS))
    return false;
  if (!func_unit_data_side
      && (op->flags & (TIC6X_FLAG_LOAD | TIC6X_FLAG_STORE)))
    return false;
  if (func_unit_data_side
      && !(op->flags & (TIC6X_FLAG_LOAD | TIC6X_FLAG_STORE)))
    return false;
  if (func_unit_data_side == 1 && (op->flags & TIC6X_FLAG_SIDE_T2_ONLY))
    return false;
  return true;
}

static tic6x_opcode_id *
filter_matching_opcodes (tic6x_opcode_list * opc_list,
			 tic6x_func_unit_base func_unit_base,
			 unsigned int func_unit_side,
			 unsigned int func_unit_cross,
			 unsigned int func_unit_data_side,
			 unsigned int *num_matching_opcodes,
			 unsigned int *max_num_operands,
			 bool num_operands_permitted[],
			 unsigned int operand_forms[], const char *str,
			 int opc_len)
{
  bool ok_this_arch = false;
  bool ok_this_fu = false;
  bool ok_this_arch_fu = false;
  unsigned int max_opcodes = 0;
  for (tic6x_opcode_list * opc = opc_list; opc; opc = opc->next)
    max_opcodes++;

  tic6x_opcode_id *opcm = XNEWVEC (tic6x_opcode_id, max_opcodes);
  *num_matching_opcodes = 0;

  for (tic6x_opcode_list * opc = opc_list; opc; opc = opc->next)
    {
      const tic6x_opcode *opct = &tic6x_opcode_table[opc->id];
      if (tic6x_insn_format_table[opct->format].num_bits != 32)
	continue;

      bool arch_ok = (opct->isa_variants & tic6x_features);
      bool fu_ok = is_opcode_fu_compatible (opct, func_unit_base,
					    func_unit_side, func_unit_cross,
					    func_unit_data_side);
      if (arch_ok)
	ok_this_arch = true;
      if (fu_ok)
	ok_this_fu = true;
      if (arch_ok && fu_ok)
	{
	  ok_this_arch_fu = true;
	  opcm[*num_matching_opcodes] = opc->id;
	  (*num_matching_opcodes)++;
	  unsigned int num_ops = opct->num_operands;
	  if (opct->flags & TIC6X_FLAG_SPMASK)
	    {
	      for (unsigned int i = 0; i < 8; i++)
		{
		  operand_forms[i] |=
		    tic6x_coarse_operand_form (tic6x_operand_func_unit);
		  num_operands_permitted[i] = true;
		}
	      num_ops = 8;
	    }
	  else
	    {
	      for (unsigned int i = 0; i < num_ops; i++)
		operand_forms[i] |=
		  tic6x_coarse_operand_form (opct->operand_info[i].form);
	    }
	  num_operands_permitted[num_ops] = true;
	  if (num_ops > *max_num_operands)
	    *max_num_operands = num_ops;
	}
    }

  if (!ok_this_arch)
    as_bad (_("'%.*s' instruction not supported on this architecture"),
	    opc_len, str);
  else if (!ok_this_fu)
    as_bad (_("'%.*s' instruction not supported on this functional unit"),
	    opc_len, str);
  else if (!ok_this_arch_fu)
    as_bad (_("'%.*s' instruction not supported on this functional unit"
	      " for this architecture"), opc_len, str);

  if (!ok_this_arch || !ok_this_fu || !ok_this_arch_fu)
    {
      free (opcm);
      return NULL;
    }
  if (*num_matching_opcodes == 0)
    abort ();

  return opcm;
}

static bool
parse_operands (char **p_ptr, tic6x_operand * operands,
		unsigned int *num_operands_read, unsigned int max_num_operands,
		const bool * num_operands_permitted,
		const unsigned int *operand_forms, const char *str,
		int opc_len)
{
  char *p = *p_ptr;
  *num_operands_read = 0;
  while (true)
    {
      skip_whitespace (p);
      if (is_end_of_stmt (*p))
	{
	  if (*num_operands_read > 0 && *(*p_ptr - 1) == ',')
	    as_bad (_("missing operand after comma"));
	  break;
	}
      if (*num_operands_read >= max_num_operands)
	{
	  as_bad (_("too many operands to '%.*s'"), opc_len, str);
	  return false;
	}

      if (!tic6x_parse_operand (&p, &operands[*num_operands_read],
				operand_forms[*num_operands_read], str,
				opc_len, *num_operands_read + 1))
	return false;
      (*num_operands_read)++;

      if (is_end_of_stmt (*p))
	break;
      if (*p == ',')
	p++;
      else
	abort ();
    }

  *p_ptr = p;

  if (!num_operands_permitted[*num_operands_read])
    {
      as_bad (_("bad number of operands to '%.*s'"), opc_len, str);
      return false;
    }
  return true;
}

static bool
validate_operands (const tic6x_operand * operands,
		   unsigned int num_operands_read,
		   const tic6x_opcode_id * opcm,
		   unsigned int num_matching_opcodes,
		   unsigned int func_unit_side, unsigned int cross_side,
		   unsigned int func_unit_data_side, const char *str,
		   int opc_len)
{
  for (unsigned int i = 0; i < num_operands_read; i++)
    {
      bool fine_ok = false;
      tic6x_operand_match fine_failure = tic6x_match_matches;
      for (unsigned int j = 0; j < num_matching_opcodes; j++)
	{
	  const tic6x_opcode *opct = &tic6x_opcode_table[opcm[j]];
	  tic6x_operand_form f;
	  tic6x_rw rw;
	  if (opct->flags & TIC6X_FLAG_SPMASK)
	    {
	      f = tic6x_operand_func_unit;
	      rw = tic6x_rw_none;
	    }
	  else
	    {
	      if (opct->num_operands != num_operands_read)
		continue;
	      f = opct->operand_info[i].form;
	      rw = opct->operand_info[i].rw;
	    }
	  if (operands[i].form != tic6x_coarse_operand_form (f))
	    continue;

	  tic6x_operand_match m = tic6x_operand_matches_form (&operands[i], f,
							      rw,
							      func_unit_side,
							      cross_side,
							      func_unit_data_side);
	  if (m == tic6x_match_matches)
	    {
	      fine_ok = true;
	      break;
	    }
	  if (fine_failure == tic6x_match_matches || fine_failure > m)
	    fine_failure = m;
	}

      if (!fine_ok)
	{
	  const char *msg;
	  switch (fine_failure)
	    {
	    case tic6x_match_non_const:
	      msg = _("operand %u of '%.*s' not constant");
	      break;
	    case tic6x_match_wrong_side:
	      msg = _("operand %u of '%.*s' on wrong side");
	      break;
	    case tic6x_match_bad_return:
	      msg = _("operand %u of '%.*s' not a valid return address register");
	      break;
	    case tic6x_match_ctrl_write_only:
	      msg = _("operand %u of '%.*s' is write-only");
	      break;
	    case tic6x_match_ctrl_read_only:
	      msg = _("operand %u of '%.*s' is read-only");
	      break;
	    case tic6x_match_bad_mem:
	      msg = _("operand %u of '%.*s' not a valid memory reference");
	      break;
	    case tic6x_match_bad_address:
	      msg = _("operand %u of '%.*s' not a valid base address register");
	      break;
	    default:
	      abort ();
	    }
	  as_bad (msg, i + 1, opc_len, str);
	  return false;
	}
    }
  return true;
}

static bool
encode_instruction (const tic6x_operand * operands,
		    unsigned int num_operands_read,
		    const tic6x_opcode_id * opcm,
		    unsigned int num_matching_opcodes, unsigned int creg,
		    unsigned int z, unsigned int side, unsigned int cross,
		    unsigned int data_side,
		    long long sploop_ii, const char *str, int opc_len,
		    const tic6x_opcode ** opct_out,
		    unsigned int *opcode_value_out, bool * fix_needed_out,
		    expressionS ** fix_exp_out, int *fix_pcrel_out,
		    bfd_reloc_code_real_type * fx_r_type_out,
		    bool * fix_adda_out)
{
  unsigned int opc_rank[TIC6X_NUM_PREFER];
  for (int i = 0; i < TIC6X_NUM_PREFER; i++)
    opc_rank[i] = -1u;
  int min_rank = TIC6X_NUM_PREFER - 1;
  int max_rank = 0;
  bool found_match = false;

  for (unsigned int i = 0; i < num_matching_opcodes; i++)
    {
      const tic6x_opcode *opct = &tic6x_opcode_table[opcm[i]];
      if (!(opct->flags & TIC6X_FLAG_SPMASK)
	  && opct->num_operands != num_operands_read)
	continue;

      bool this_matches = true;
      for (unsigned int j = 0; j < num_operands_read; j++)
	{
	  tic6x_operand_form f;
	  tic6x_rw rw;
	  if (opct->flags & TIC6X_FLAG_SPMASK)
	    {
	      f = tic6x_operand_func_unit;
	      rw = tic6x_rw_none;
	    }
	  else
	    {
	      f = opct->operand_info[j].form;
	      rw = opct->operand_info[j].rw;
	    }
	  if (tic6x_operand_matches_form (&operands[j], f, rw, side,
					  (cross ? 3 - side : side),
					  data_side) != tic6x_match_matches)
	    {
	      this_matches = false;
	      break;
	    }
	}

      if (this_matches)
	{
	  found_match = true;
	  int rank = TIC6X_PREFER_VAL (opct->flags);
	  if (rank < min_rank)
	    min_rank = rank;
	  if (rank > max_rank)
	    max_rank = rank;
	  if (opc_rank[rank] != -1u)
	    abort ();
	  opc_rank[rank] = i;
	}
    }

  if (!found_match)
    {
      as_bad (_("bad operand combination for '%.*s'"), opc_len, str);
      return false;
    }

  for (int rank = max_rank; rank >= min_rank; rank--)
    {
      if (opc_rank[rank] == -1u)
	continue;
      bool encoded_ok = false;
      unsigned int opcode_value = tic6x_try_encode (opcm[opc_rank[rank]],
						    operands,
						    num_operands_read, creg, z,
						    side, cross, data_side,
						    sploop_ii, fix_exp_out,
						    fix_pcrel_out,
						    fx_r_type_out,
						    fix_adda_out,
						    fix_needed_out, &encoded_ok,
						    rank == min_rank, str,
						    opc_len);
      if (encoded_ok)
	{
	  *opct_out = &tic6x_opcode_table[opcm[opc_rank[rank]]];
	  *opcode_value_out = opcode_value;
	  return true;
	}
    }

  return false;
}

static char *
get_output_frag_buffer (segment_info_type * seginfo,
			bool this_line_parallel,
			tic6x_label_list * this_insn_label_list,
			const tic6x_opcode * opct, const char *str,
			int opc_len, fragS ** insn_frag_ptr)
{
  if (this_line_parallel)
    {
      *insn_frag_ptr = seginfo->tc_segment_info_data.execute_packet_frag;
      if (!*insn_frag_ptr)
	{
	  as_bad (_("parallel instruction not following another instruction"));
	  return NULL;
	}
      if ((*insn_frag_ptr)->fr_fix >= 32)
	{
	  as_bad (_("too many instructions in execute packet"));
	  return NULL;
	}
      if (this_insn_label_list)
	as_bad (_("label not at start of execute packet"));
      if (opct->flags & TIC6X_FLAG_FIRST)
	as_bad (_("'%.*s' instruction not at start of execute packet"),
		opc_len, str);

      *seginfo->tc_segment_info_data.last_insn_lsb |= 0x1;
      return (*insn_frag_ptr)->fr_literal + (*insn_frag_ptr)->fr_fix;
    }
  else
    {
      seginfo->tc_segment_info_data.spmask_addr = NULL;
      seginfo->tc_segment_info_data.func_units_used = 0;

      if (frag_now_fix () != 0)
	{
	  if (frag_now->fr_type != rs_machine_dependent)
	    frag_wane (frag_now);
	  frag_new (0);
	}
      frag_grow (32);
      *insn_frag_ptr = seginfo->tc_segment_info_data.execute_packet_frag =
	frag_now;

      for (tic6x_label_list * l = this_insn_label_list; l; l = l->next)
	{
	  symbol_set_frag (l->label, frag_now);
	  S_SET_VALUE (l->label, 0);
	  S_SET_SEGMENT (l->label, now_seg);
	}
      tic6x_free_label_list (this_insn_label_list);
      dwarf2_emit_insn (0);
      char *output =
	frag_var (rs_machine_dependent, 32, 32, 0, NULL, 0, NULL);
      if (output != (*insn_frag_ptr)->fr_literal)
	abort ();
      (*insn_frag_ptr)->tc_frag_data.is_insns = true;
      (*insn_frag_ptr)->tc_frag_data.can_cross_fp_boundary =
	tic6x_can_cross_fp_boundary;
      return output;
    }
}

static void
update_state_after_emission (segment_info_type * seginfo,
			     const tic6x_opcode * opct,
			     tic6x_func_unit_base func_unit_base,
			     unsigned int func_unit_side,
			     bool this_line_spmask,
			     const tic6x_operand * operands,
			     unsigned int num_operands_read,
			     const char *str, int opc_len, char *output)
{
  if (func_unit_base != tic6x_func_unit_nfu)
    {
      unsigned int func_unit_enc =
	tic6x_encode_spmask (func_unit_base, func_unit_side);
      if (seginfo->tc_segment_info_data.func_units_used & func_unit_enc)
	as_bad (_("functional unit already used in this execute packet"));
      seginfo->tc_segment_info_data.func_units_used |= func_unit_enc;
    }

  if (opct->flags & TIC6X_FLAG_SPLOOP)
    {
      if (seginfo->tc_segment_info_data.sploop_ii)
	as_bad (_("nested software pipelined loop"));
      if (num_operands_read != 1
	  || operands[0].form != TIC6X_OP_EXP
	  || operands[0].value.exp.X_op != O_constant)
	abort ();
      seginfo->tc_segment_info_data.sploop_ii =
	operands[0].value.exp.X_add_number;
    }
  else if (opct->flags & TIC6X_FLAG_SPKERNEL)
    {
      if (!seginfo->tc_segment_info_data.sploop_ii)
	as_bad (_("'%.*s' instruction not in a software pipelined loop"),
		opc_len, str);
      seginfo->tc_segment_info_data.sploop_ii = 0;
    }

  if (this_line_spmask)
    {
      if (!seginfo->tc_segment_info_data.spmask_addr)
	as_bad (_("'||^' without previous SPMASK"));
      else if (func_unit_base == tic6x_func_unit_nfu)
	as_bad (_("cannot mask instruction using no functional unit"));
      else
	{
	  unsigned int mask_bit =
	    tic6x_encode_spmask (func_unit_base,
				 func_unit_side) << 18;
	  char *addr = seginfo->tc_segment_info_data.spmask_addr;
	  unsigned int spmask_op = md_chars_to_number (addr, 4);
	  if (spmask_op & mask_bit)
	    as_bad (_("functional unit already masked"));
	  md_number_to_chars (addr, spmask_op | mask_bit, 4);
	}
    }

  if (opct->flags & TIC6X_FLAG_SPMASK)
    seginfo->tc_segment_info_data.spmask_addr = output;
}

void
md_assemble (char *str)
{
  char *p = str;
  int opc_len;
  initialize_assembly (&p, str, &opc_len);

  const bool this_line_parallel = tic6x_line_parallel;
  const bool this_line_spmask = tic6x_line_spmask;
  const unsigned int this_line_creg = tic6x_line_creg;
  const unsigned int this_line_z = tic6x_line_z;

  tic6x_line_parallel = false;
  tic6x_line_spmask = false;
  tic6x_line_creg = 0;
  tic6x_line_z = 0;

  segment_info_type *seginfo = seg_info (now_seg);
  tic6x_label_list *this_insn_label_list =
    seginfo->tc_segment_info_data.label_list;
  seginfo->tc_segment_info_data.label_list = NULL;

  tic6x_opcode_list *opc_list =
    str_hash_find_n (opcode_hash, str, opc_len);
  if (!opc_list)
    {
      as_bad (_("unknown opcode '%.*s'"), opc_len, str);
      return;
    }

  tic6x_func_unit_base func_unit_base = tic6x_func_unit_nfu;
  unsigned int func_unit_side = 0;
  unsigned int func_unit_cross = 0;
  unsigned int cross_side = 0;
  unsigned int func_unit_data_side = 0;
  parse_functional_unit (&p, &func_unit_base, &func_unit_side,
			 &func_unit_cross, &cross_side, &func_unit_data_side);

  unsigned int max_num_operands = 0;
  unsigned int num_matching_opcodes = 0;
  bool num_operands_permitted[TIC6X_MAX_SOURCE_OPERANDS + 1] = { false };
  unsigned int operand_forms[TIC6X_MAX_SOURCE_OPERANDS] = { 0 };

  tic6x_opcode_id *opcm =
    filter_matching_opcodes (opc_list, func_unit_base, func_unit_side,
			     func_unit_cross, func_unit_data_side,
			     &num_matching_opcodes, &max_num_operands,
			     num_operands_permitted, operand_forms, str,
			     opc_len);
  if (!opcm)
    return;

  tic6x_operand operands[TIC6X_MAX_SOURCE_OPERANDS];
  unsigned int num_operands_read;
  if (!parse_operands (&p, operands, &num_operands_read, max_num_operands,
		       num_operands_permitted, operand_forms, str, opc_len)
      || !validate_operands (operands, num_operands_read, opcm,
			     num_matching_opcodes, func_unit_side, cross_side,
			     func_unit_data_side, str, opc_len))
    {
      free (opcm);
      return;
    }

  const tic6x_opcode *opct = NULL;
  unsigned int opcode_value = 0;
  bool fix_needed = false;
  expressionS *fix_exp = NULL;
  int fix_pcrel = 0;
  bfd_reloc_code_real_type fx_r_type = BFD_RELOC_UNUSED;
  bool fix_adda = false;

  if (!encode_instruction (operands, num_operands_read, opcm,
			   num_matching_opcodes, this_line_creg, this_line_z,
			   func_unit_side, func_unit_cross,
			   func_unit_data_side,
			   seginfo->tc_segment_info_data.sploop_ii, str,
			   opc_len, &opct, &opcode_value, &fix_needed,
			   &fix_exp, &fix_pcrel, &fx_r_type, &fix_adda))
    {
      free (opcm);
      return;
    }
  free (opcm);

  fragS *insn_frag;
  char *output = get_output_frag_buffer (seginfo, this_line_parallel,
					 this_insn_label_list, opct, str,
					 opc_len, &insn_frag);
  if (!output)
    return;

  update_state_after_emission (seginfo, opct, func_unit_base, func_unit_side,
			       this_line_spmask, operands, num_operands_read,
			       str, opc_len, output);

  record_alignment (now_seg, 5);
  md_number_to_chars (output, opcode_value, 4);
  if (fix_needed)
    tic6x_fix_new_exp (insn_frag, output - insn_frag->fr_literal, 4, fix_exp,
		       fix_pcrel, fx_r_type, fix_adda);

  insn_frag->fr_fix += 4;
  insn_frag->fr_var -= 4;
  seginfo->tc_segment_info_data.last_insn_lsb =
    (target_big_endian ? output + 3 : output);
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
md_apply_fix (fixS *fixP, valueT *valP, segT seg)
{
  valueT value = *valP;
  char *buf = fixP->fx_where + fixP->fx_frag->fr_literal;
  const int should_apply_fix = fixP->fx_done || !seg->use_rela_p;

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
      if (should_apply_fix)
	md_number_to_chars (buf, value, 4);
      break;

    case BFD_RELOC_16:
      if (should_apply_fix)
	{
	  if (value < -0x8000 || value > 0x7FFF)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("value too large for 2-byte field"));
	  md_number_to_chars (buf, value, 2);
	}
      break;

    case BFD_RELOC_8:
      if (should_apply_fix)
	{
	  if (value < -0x80 || value > 0x7F)
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
      {
	if (should_apply_fix)
	  {
	    valueT newval = md_chars_to_number (buf, 4);
	    int shift = 0;

	    if (fixP->fx_r_type == BFD_RELOC_C6000_SBR_L16_H)
	      shift = 1;
	    else if (fixP->fx_r_type == BFD_RELOC_C6000_SBR_L16_W
		     || fixP->fx_r_type == BFD_RELOC_C6000_SBR_GOT_L16_W)
	      shift = 2;

	    MODIFY_VALUE (newval, value, shift, 7, 16);
	    if ((fixP->fx_r_type == BFD_RELOC_C6000_ABS_S16
		 || fixP->fx_r_type == BFD_RELOC_C6000_SBR_S16)
		&& (value < -0x8000 || value > 0x7FFF))
	      as_bad_where (fixP->fx_file, fixP->fx_line,
			    _("immediate offset out of range"));

	    md_number_to_chars (buf, newval, 4);
	  }
	if (fixP->fx_done
	    && fixP->fx_r_type != BFD_RELOC_C6000_ABS_S16
	    && fixP->fx_r_type != BFD_RELOC_C6000_ABS_L16)
	  abort ();
      }
      break;

    case BFD_RELOC_C6000_ABS_H16:
    case BFD_RELOC_C6000_SBR_H16_B:
    case BFD_RELOC_C6000_SBR_H16_H:
    case BFD_RELOC_C6000_SBR_H16_W:
    case BFD_RELOC_C6000_SBR_GOT_H16_W:
      {
	if (should_apply_fix)
	  {
	    valueT newval = md_chars_to_number (buf, 4);
	    int shift = 16;

	    if (fixP->fx_r_type == BFD_RELOC_C6000_SBR_H16_H)
	      shift = 17;
	    else if (fixP->fx_r_type == BFD_RELOC_C6000_SBR_H16_W
		     || fixP->fx_r_type == BFD_RELOC_C6000_SBR_GOT_H16_W)
	      shift = 18;

	    MODIFY_VALUE (newval, value, shift, 7, 16);
	    md_number_to_chars (buf, newval, 4);
	  }
	if (fixP->fx_done && fixP->fx_r_type != BFD_RELOC_C6000_ABS_H16)
	  abort ();
      }
      break;

    case BFD_RELOC_C6000_PCR_H16:
    case BFD_RELOC_C6000_PCR_L16:
      if (should_apply_fix)
	{
	  valueT newval = md_chars_to_number (buf, 4);
	  const int shift = (fixP->fx_r_type == BFD_RELOC_C6000_PCR_H16) ? 16 : 0;
	  MODIFY_VALUE (newval, value, shift, 7, 16);
	  md_number_to_chars (buf, newval, 4);
	}
      break;

    case BFD_RELOC_C6000_SBR_U15_B:
      if (should_apply_fix)
	{
	  valueT newval = md_chars_to_number (buf, 4);
	  MODIFY_VALUE (newval, value, 0, 8, 15);
	  if (value > 0x7FFF)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("immediate offset out of range"));
	  md_number_to_chars (buf, newval, 4);
	}
      break;

    case BFD_RELOC_C6000_SBR_U15_H:
      if (should_apply_fix)
	{
	  valueT temp_val = value;
	  valueT newval = md_chars_to_number (buf, 4);

	  if (fixP->tc_fix_data.fix_adda && fixP->fx_done)
	    temp_val <<= 1;

	  MODIFY_VALUE (newval, temp_val, 1, 8, 15);
	  if (temp_val & 1)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("immediate offset not 2-byte-aligned"));
	  if (temp_val > 0xFFFE)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("immediate offset out of range"));
	  md_number_to_chars (buf, newval, 4);
	}
      break;

    case BFD_RELOC_C6000_SBR_U15_W:
    case BFD_RELOC_C6000_SBR_GOT_U15_W:
      {
	if (should_apply_fix)
	  {
	    valueT temp_val = value;
	    valueT newval = md_chars_to_number (buf, 4);

	    if (fixP->tc_fix_data.fix_adda && fixP->fx_done)
	      temp_val <<= 2;

	    MODIFY_VALUE (newval, temp_val, 2, 8, 15);
	    if (temp_val & 3)
	      as_bad_where (fixP->fx_file, fixP->fx_line,
			    _("immediate offset not 4-byte-aligned"));
	    if (temp_val > 0x1FFFC)
	      as_bad_where (fixP->fx_file, fixP->fx_line,
			    _("immediate offset out of range"));
	    md_number_to_chars (buf, newval, 4);
	  }
	if (fixP->fx_done && fixP->fx_r_type != BFD_RELOC_C6000_SBR_U15_W)
	  abort ();
      }
      break;

    case BFD_RELOC_C6000_DSBT_INDEX:
      if (value != 0)
	as_bad_where (fixP->fx_file, fixP->fx_line,
		      _("addend used with $DSBT_INDEX"));
      if (fixP->fx_done)
	abort ();
      break;

    case BFD_RELOC_C6000_PCR_S21:
      if (should_apply_fix)
	{
	  valueT newval = md_chars_to_number (buf, 4);
	  MODIFY_VALUE (newval, value, 2, 7, 21);
	  if (value & 3)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("PC-relative offset not 4-byte-aligned"));
	  if (value < -0x400000 || value > 0x3FFFFC)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("PC-relative offset out of range"));
	  md_number_to_chars (buf, newval, 4);
	}
      break;

    case BFD_RELOC_C6000_PCR_S12:
      if (should_apply_fix)
	{
	  valueT newval = md_chars_to_number (buf, 4);
	  MODIFY_VALUE (newval, value, 2, 16, 12);
	  if (value & 3)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("PC-relative offset not 4-byte-aligned"));
	  if (value < -0x2000 || value > 0x1FFC)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("PC-relative offset out of range"));
	  md_number_to_chars (buf, newval, 4);
	}
      break;

    case BFD_RELOC_C6000_PCR_S10:
      if (should_apply_fix)
	{
	  valueT newval = md_chars_to_number (buf, 4);
	  MODIFY_VALUE (newval, value, 2, 13, 10);
	  if (value & 3)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("PC-relative offset not 4-byte-aligned"));
	  if (value < -0x800 || value > 0x7FC)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("PC-relative offset out of range"));
	  md_number_to_chars (buf, newval, 4);
	}
      break;

    case BFD_RELOC_C6000_PCR_S7:
      if (should_apply_fix)
	{
	  valueT newval = md_chars_to_number (buf, 4);
	  MODIFY_VALUE (newval, value, 2, 16, 7);
	  if (value & 3)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("PC-relative offset not 4-byte-aligned"));
	  if (value < -0x100 || value > 0xFC)
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
md_atof(int type, char *litP, int *sizeP)
{
    if (litP == NULL || sizeP == NULL)
    {
        return "Invalid NULL pointer argument";
    }

    return ieee_md_atof(type, litP, sizeP, target_big_endian);
}

/* Adjust the frags in SECTION (see tic6x_md_finish).  */

typedef struct
{
  frchainS *frchp;
  fragS *fragp;
  unsigned int pos;
} alignment_state_type;

static void
update_alignment_state (alignment_state_type *state, frchainS *frchp,
			fragS *fragp, unsigned int pos)
{
  state->frchp = frchp;
  state->fragp = fragp;
  state->pos = pos;
}

static void
rewind_state (const alignment_state_type *state, frchainS **frchp_p,
	      fragS **fragp_p, unsigned int *pos_p)
{
  *frchp_p = state->frchp;
  *fragp_p = state->fragp;
  *pos_p = state->pos;
}

static void
insert_nops_into_frag (fragS *fragp, unsigned int count)
{
  for (unsigned int i = 0; i < count; i++)
    {
      md_number_to_chars (fragp->fr_literal + fragp->fr_fix, 0, 4);
      if (target_big_endian)
	fragp->fr_literal[fragp->fr_fix - 1] |= 0x1;
      else
	fragp->fr_literal[fragp->fr_fix - 4] |= 0x1;
      fragp->fr_fix += 4;
      fragp->fr_var -= 4;
    }
}

static unsigned int
get_needed_nops_for_frag (const fragS *fragp, unsigned int pos)
{
  if (fragp->tc_frag_data.is_insns)
    {
      if (pos + fragp->fr_fix > 32
	  && !fragp->tc_frag_data.can_cross_fp_boundary)
	{
	  if (pos & 3)
	    abort ();
	  unsigned int nops = (32 - pos) >> 2;
	  if (nops > 7)
	    abort ();
	  return nops;
	}
    }
  else
    {
      unsigned int align_val = 1 << fragp->fr_offset;
      unsigned int align_mask = align_val - 1;
      if (pos & align_mask)
	{
	  unsigned int would_insert_bytes = align_val - (pos & align_mask);
	  if (fragp->fr_subtype == 0
	      || would_insert_bytes <= fragp->fr_subtype)
	    {
	      if (fragp->fr_offset < 3 || fragp->fr_offset > 5)
		abort ();
	      if (would_insert_bytes & 3)
		abort ();
	      unsigned int nops = would_insert_bytes >> 2;
	      if (nops > 7)
		abort ();
	      return nops;
	    }
	}
    }
  return 0;
}

static void
process_code_only_section_alignment (segment_info_type *info)
{
  unsigned int want_insert = 0;
  unsigned int want_insert_done_so_far = 0;
  unsigned int pos = 0;
  alignment_state_type last32, last16, last8;

  frchainS *frchp = info->frchainP;
  fragS *fragp = frchp ? frchp->frch_root : NULL;

  update_alignment_state (&last32, frchp, fragp, 0);
  last16 = last8 = last32;

  while (fragp)
    {
      bool needs_rewind = false;
      frchainS *next_frchp = frchp;
      fragS *next_fragp = fragp->fr_next;

      if (!next_fragp)
	{
	  next_frchp = frchp->frch_next;
	  if (next_frchp)
	    next_fragp = next_frchp->frch_root;
	}

      if (fragp->fr_type == rs_machine_dependent)
	{
	  if (want_insert == 0)
	    {
	      unsigned int needed_nops = get_needed_nops_for_frag (fragp, pos);
	      if (needed_nops > 0)
		{
		  if (want_insert)
		    abort ();
		  want_insert = needed_nops;
		  want_insert_done_so_far = 0;
		  needs_rewind = true;
		}
	    }
	  else if (fragp->tc_frag_data.is_insns)
	    {
	      unsigned int num_insns = fragp->fr_fix >> 2;
	      unsigned int max_poss_nops = (num_insns < 8) ? (8 - num_insns) : 0;
	      if (max_poss_nops > 0)
		{
		  unsigned int cur_want_nops = want_insert & -want_insert;
		  if (cur_want_nops == 0)
		    abort ();
		  unsigned int max_want_nops
		    = cur_want_nops - want_insert_done_so_far;
		  unsigned int do_nops
		    = (max_poss_nops < max_want_nops ? max_poss_nops
						    : max_want_nops);
		  if (do_nops > 0)
		    {
		      insert_nops_into_frag (fragp, do_nops);
		      want_insert_done_so_far += do_nops;
		    }
		  if (want_insert_done_so_far == cur_want_nops)
		    {
		      want_insert -= want_insert_done_so_far;
		      want_insert_done_so_far = 0;
		      if (want_insert > 0)
			needs_rewind = true;
		    }
		}
	    }
	}

      if (needs_rewind)
	{
	  unsigned int current_stage = want_insert & -want_insert;
	  if (current_stage == 1)
	    {
	      rewind_state (&last8, &frchp, &fragp, &pos);
	    }
	  else if (current_stage == 2)
	    {
	      rewind_state (&last16, &frchp, &fragp, &pos);
	      last8 = last16;
	    }
	  else if (current_stage == 4)
	    {
	      rewind_state (&last32, &frchp, &fragp, &pos);
	      last16 = last8 = last32;
	    }
	  else if (want_insert > 0)
	    {
	      abort ();
	    }
	  continue;
	}

      if (fragp->fr_type == rs_machine_dependent)
	{
	  pos = (pos + fragp->fr_fix) & 31;
	  if ((pos & 7) == 0)
	    update_alignment_state (&last8, next_frchp, next_fragp, pos);
	  if ((pos & 15) == 0)
	    update_alignment_state (&last16, next_frchp, next_fragp, pos);
	  if ((pos & 31) == 0)
	    update_alignment_state (&last32, next_frchp, next_fragp, pos);
	}
      frchp = next_frchp;
      fragp = next_fragp;
    }
}

static void
tic6x_adjust_section (bfd *abfd ATTRIBUTE_UNUSED, segT section,
		      void *dummy ATTRIBUTE_UNUSED)
{
  segment_info_type *info;
  frchainS *frchp;
  fragS *fragp;
  bool have_code = false;
  bool have_non_code = false;

  info = seg_info (section);
  if (info == NULL)
    return;

  for (frchp = info->frchainP; frchp; frchp = frchp->frch_next)
    for (fragp = frchp->frch_root; fragp; fragp = fragp->fr_next)
      switch (fragp->fr_type)
	{
	case rs_machine_dependent:
	  if (fragp->tc_frag_data.is_insns)
	    have_code = true;
	  break;

	case rs_dummy:
	case rs_fill:
	  if (fragp->fr_fix > 0)
	    have_non_code = true;
	  break;

	default:
	  have_non_code = true;
	  break;
	}

  if (have_code && !have_non_code)
    {
      process_code_only_section_alignment (info);
    }

  for (frchp = info->frchainP; frchp; frchp = frchp->frch_next)
    for (fragp = frchp->frch_root; fragp; fragp = fragp->fr_next)
      {
	if (fragp->fr_type == rs_machine_dependent)
	  {
	    if (fragp->tc_frag_data.is_insns)
	      frag_wane (fragp);
	    else
	      {
		fragp->fr_type = rs_align_code;
		fragp->fr_var = 1;
		*fragp->fr_literal = 0;
	      }
	  }
      }
}

/* Initialize the machine-dependent parts of a frag.  */

void
tic6x_frag_init (fragS *fragp)
{
  if (fragp)
    {
      fragp->tc_frag_data.is_insns = false;
      fragp->tc_frag_data.can_cross_fp_boundary = false;
    }
}

/* Set an attribute if it has not already been set by the user.  */

static void
tic6x_set_attribute_int (int tag, int value)
{
  if (tag < 1 || tag >= NUM_KNOWN_OBJ_ATTRIBUTES)
    {
      as_fatal (_("internal error: invalid attribute tag: %d"), tag);
    }

  if (tic6x_attributes_set_explicitly[tag])
    {
      return;
    }

  if (!bfd_elf_add_proc_attr_int (stdoutput, tag, value))
    {
      as_fatal (_("error adding attribute: %s"),
                bfd_errmsg (bfd_get_error ()));
    }
}

/* Set object attributes deduced from the input file and command line
   rather than given explicitly.  */
static void
tic6x_set_attributes (void)
{
  if (tic6x_arch_attribute == C6XABI_Tag_ISA_none)
    {
      tic6x_arch_attribute = C6XABI_Tag_ISA_C674X;
    }

  const struct { int tag; int value; } attributes_to_set[] = {
    {Tag_ISA, tic6x_arch_attribute},
    {Tag_ABI_DSBT, tic6x_dsbt},
    {Tag_ABI_PID, tic6x_pid},
    {Tag_ABI_PIC, tic6x_pic}
  };

  for (size_t i = 0; i < sizeof (attributes_to_set) / sizeof (attributes_to_set[0]); ++i)
    {
      tic6x_set_attribute_int (attributes_to_set[i].tag, attributes_to_set[i].value);
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
      bfd_perror ("section layout and optimization failed");
      exit (EXIT_FAILURE);
    }
}

/* No machine-dependent frags at this stage; all converted in
   tic6x_md_finish.  */

#include <stdio.h>
#include <stdlib.h>
#include <stdnoreturn.h>

noreturn void
md_convert_frag (bfd *abfd ATTRIBUTE_UNUSED, segT asec ATTRIBUTE_UNUSED,
                 fragS *fragp ATTRIBUTE_UNUSED);

void
md_convert_frag (bfd *abfd ATTRIBUTE_UNUSED, segT asec ATTRIBUTE_UNUSED,
                 fragS *fragp ATTRIBUTE_UNUSED)
{
  fprintf (stderr, "FATAL: Unimplemented function %s called.\n", __func__);
  abort ();
}

/* No machine-dependent frags at this stage; all converted in
   tic6x_md_finish.  */

void
md_estimate_size_before_relax (fragS *fragp ATTRIBUTE_UNUSED,
			       segT seg ATTRIBUTE_UNUSED) ATTRIBUTE_NORETURN;

void
md_estimate_size_before_relax (fragS *fragp ATTRIBUTE_UNUSED,
			       segT seg ATTRIBUTE_UNUSED)
{
  abort ();
}

/* Put a number into target byte order.  */

void
md_number_to_chars (char *buf, valueT val, int n)
{
    if (!buf || n <= 0 || n > sizeof(valueT))
    {
        return;
    }

    if (target_big_endian)
    {
        number_to_chars_bigendian(buf, val, n);
    }
    else
    {
        number_to_chars_littleendian(buf, val, n);
    }
}

/* Machine-dependent operand parsing not currently needed.  */

void
md_operand (expressionS *op)
{
  (void) op;
}

/* PC-relative operands are relative to the start of the fetch
   packet.  */

long
tic6x_pcrel_from_section (fixS *fixp, segT sec)
{
  static const unsigned long long TIC6X_ALIGNMENT_MASK = ~0x1fULL;
  symbolS * const symbol = fixp->fx_addsy;

  if (symbol != NULL)
    {
      const int is_undefined = !S_IS_DEFINED (symbol);
      const int is_wrong_segment = S_GET_SEGMENT (symbol) != sec;

      if (is_undefined || is_wrong_segment)
        {
          return 0;
        }
    }

  const unsigned long long pcrel_base = (unsigned long long)fixp->fx_where + fixp->fx_frag->fr_address;
  const unsigned long long aligned_base = pcrel_base & TIC6X_ALIGNMENT_MASK;

  return (long) aligned_base;
}

/* Round up a section size to the appropriate boundary.  */

#include <stddef.h>

typedef size_t valueT;
typedef const void *segT;
#define ATTRIBUTE_UNUSED __attribute__((unused))

extern int bfd_section_alignment(segT);

valueT
md_section_align (segT segment ATTRIBUTE_UNUSED,
		  valueT size)
{
  int align = bfd_section_alignment (segment);

  if (align <= 0)
    {
      return size;
    }

  if ((unsigned int)align >= (sizeof (valueT) * 8))
    {
      return size;
    }

  const valueT alignment = (valueT)1 << align;
  const valueT mask = alignment - 1;

  return (size + mask) & ~mask;
}

/* No special undefined symbol handling needed for now.  */

symbolS *
md_undefined_symbol (const char *name ATTRIBUTE_UNUSED)
{
  return NULL;
}

/* Translate internal representation of relocation info to BFD target
   format.  */

static void
adjust_pcrel_addend (arelent *reloc, const asymbol *symbol)
{
  if (reloc->howto->pcrel_offset && reloc->howto->partial_inplace)
    {
      reloc->addend += reloc->address;
      if (!bfd_is_com_section (bfd_asymbol_section (symbol)))
	{
	  reloc->addend -= symbol->value;
	}
    }
}

static void
handle_c6000_pcr_reloc (arelent *reloc, const fixS *fixp)
{
  symbolS *sub_symbol = fixp->tc_fix_data.fix_subsy;
  resolve_symbol_value (sub_symbol);
  segT sub_symbol_segment = S_GET_SEGMENT (sub_symbol);

  if (sub_symbol_segment == undefined_section)
    {
      as_bad_where (fixp->fx_file, fixp->fx_line,
		    _("undefined symbol %s in PCR relocation"),
		    S_GET_NAME (sub_symbol));
    }
  else
    {
      reloc->addend = (reloc->address & ~0x1F) - S_GET_VALUE (sub_symbol);
    }
}

arelent *
tc_gen_reloc (asection *section ATTRIBUTE_UNUSED, fixS *fixp)
{
  arelent *reloc = notes_alloc (sizeof (arelent));
  if (!reloc)
    {
      return NULL;
    }

  reloc->sym_ptr_ptr = notes_alloc (sizeof (asymbol *));
  if (!reloc->sym_ptr_ptr)
    {
      return NULL;
    }

  asymbol *symbol = symbol_get_bfdsym (fixp->fx_addsy);
  *reloc->sym_ptr_ptr = symbol;

  reloc->address = fixp->fx_frag->fr_address + fixp->fx_where;
  reloc->addend = tic6x_generate_rela ? fixp->fx_offset : 0;

  const bfd_reloc_code_real_type r_type = fixp->fx_r_type;
  reloc->howto = bfd_reloc_type_lookup (stdoutput, r_type);

  if (!reloc->howto)
    {
      as_bad_where (fixp->fx_file, fixp->fx_line,
		    _("Cannot represent relocation type %s"),
		    bfd_get_reloc_code_name (r_type));
      return NULL;
    }

  adjust_pcrel_addend (reloc, symbol);

  if (r_type == BFD_RELOC_C6000_PCR_H16
      || r_type == BFD_RELOC_C6000_PCR_L16)
    {
      handle_c6000_pcr_reloc (reloc, fixp);
    }

  return reloc;
}

/* Convert REGNAME to a DWARF-2 register number.  */

int
tic6x_regname_to_dw2regnum (char *regname)
{
  tic6x_register reg;
  char *p = regname;

  if (!tic6x_parse_register (&p, &reg))
    {
      return -1;
    }

  if (reg.num < 0 || reg.num >= 32)
    {
      return -1;
    }

  switch (reg.side)
    {
    case 1: /* A regs.  */
      return (reg.num < 16) ? reg.num : (reg.num - 16) + 37;

    case 2: /* B regs.  */
      return (reg.num < 16) ? reg.num + 16 : (reg.num - 16) + 53;
    }

  return -1;
}

/* Initialize the DWARF-2 unwind information for this procedure.  */

#define TIC6X_STACK_POINTER_REGNUM 31
#define INITIAL_CFA_OFFSET 0

void
tic6x_frame_initial_instructions (void)
{
  /*
   * Define the initial Canonical Frame Address (CFA) as the
   * stack pointer register (B15) with a zero offset.
   */
  cfi_add_CFA_def_cfa (TIC6X_STACK_POINTER_REGNUM, INITIAL_CFA_OFFSET);
}

/* Start an exception table entry.  If idx is nonzero this is an index table
   entry.  */

static void
tic6x_start_unwind_section (const segT text_seg, int idx)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();
  const char *text_name_base = segment_name (text_seg);
  const char *text_name_suffix;
  int is_gnu_linkonce = 0;
  struct elf_section_match match;

  const char *prefix = idx ? ELF_STRING_C6000_unwind : ELF_STRING_C6000_unwind_info;
  const char *prefix_once = idx ? ELF_STRING_C6000_unwind_once : ELF_STRING_C6000_unwind_info_once;
  int type = idx ? SHT_C6000_UNWIND : SHT_PROGBITS;

  if (streq (text_name_base, ".text"))
    {
      text_name_suffix = "";
    }
  else if (startswith (text_name_base, ".gnu.linkonce.t."))
    {
      prefix = prefix_once;
      text_name_suffix = text_name_base + strlen (".gnu.linkonce.t.");
      is_gnu_linkonce = 1;
    }
  else
    {
      text_name_suffix = text_name_base;
    }

  size_t prefix_len = strlen (prefix);
  size_t text_len = strlen (text_name_suffix);
  char *sec_name = XNEWVEC (char, prefix_len + text_len + 1);
  memcpy (sec_name, prefix, prefix_len);
  memcpy (sec_name + prefix_len, text_name_suffix, text_len + 1);

  int flags = SHF_ALLOC;
  int is_comdat = 0;
  memset (&match, 0, sizeof (match));

  if (!is_gnu_linkonce && (text_seg->flags & SEC_LINK_ONCE) != 0)
    {
      match.group_name = elf_group_name (text_seg);
      if (match.group_name == NULL)
	{
	  as_bad (_("group section `%s' has no group signature"),
		  segment_name (text_seg));
	  ignore_rest_of_line ();
	  return;
	}
      flags |= SHF_GROUP;
      is_comdat = 1;
    }

  obj_elf_change_section (sec_name, type, flags, 0, &match, is_comdat);

  if (idx)
    {
      elf_linked_to_section (now_seg) = text_seg;
    }

  seg_info (now_seg)->tc_segment_info_data.text_unwind = unwind;
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
static int tic6x_unwind_reg_from_dwarf(int dwarf)
{
    for (int reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++) {
        if (tic6x_unwind_frame_regs[reg] == dwarf) {
            return reg;
        }
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
  if (unwind == NULL)
    {
      return;
    }

  const int is_new_entry = (unwind->table_entry == NULL);
  if (is_new_entry)
    {
      /* Create EXTAB entry if it does not exist.  */
      tic6x_start_unwind_section (unwind->saved_seg, 0);
      frag_align (2, 0, 0);
      record_alignment (now_seg, 2);
      unwind->table_entry = expr_build_dot ();
    }

  char *ptr = frag_more (4);
  if (ptr == NULL)
    {
      return;
    }

  if (is_new_entry)
    {
      unwind->frag_start = ptr;
    }

  md_number_to_chars (ptr, data, 4);
}

/* Add a single byte of unwinding data.  */

static void
tic6x_unwind_byte (int byte)
{
  const int bytes_per_word = 4;
  const int pr1_transition_byte_count = 5;
  const int no_personality_index = -1;
  const int pr1_index = 1;
  const unsigned int pr1_header = 0x81000000;
  const unsigned int pr1_data_mask = 0xffff;
  const int pr1_data_shift = 8;
  const unsigned int last_byte_mask = 0xff;

  tic6x_unwind_info *unwind = tic6x_get_unwind ();
  if (unwind == NULL)
    {
      return;
    }

  unwind->data_bytes++;

  if (unwind->data_bytes == pr1_transition_byte_count)
    {
      if (unwind->personality_index == no_personality_index)
        {
          unwind->personality_index = pr1_index;
          unsigned int header_data = (unwind->data >> pr1_data_shift) & pr1_data_mask;
          tic6x_flush_unwind_word (pr1_header | header_data);

          unsigned int last_byte_of_word = unwind->data & last_byte_mask;
          unwind->data = (last_byte_of_word << 8) | (unsigned int) byte;
          unwind->data_bytes++;
        }
      else
        {
          tic6x_flush_unwind_word (unwind->data);
          unwind->data = (unsigned int) byte;
        }
    }
  else
    {
      unwind->data = (unwind->data << 8) | (unsigned int) byte;
      if (unwind->data_bytes > bytes_per_word
          && (unwind->data_bytes & (bytes_per_word - 1)) == 0)
        {
          tic6x_flush_unwind_word (unwind->data);
          unwind->data = 0;
        }
    }
}

/* Add a two-byte unwinding opcode.  */
static void
tic6x_unwind_2byte (uint16_t value)
{
  tic6x_unwind_byte (value >> 8);
  tic6x_unwind_byte (value & 0xFF);
}

static void
tic6x_unwind_uleb (offsetT offset)
{
  do
    {
      unsigned char byte = offset & 0x7f;
      offset >>= 7;
      if (offset != 0)
        {
          byte |= 0x80;
        }
      tic6x_unwind_byte (byte);
    }
  while (offset != 0);
}

void
tic6x_cfi_startproc (void)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();

  if (!unwind)
    {
      return;
    }

  if (unwind->table_entry)
    {
      as_bad (_("missing .endp before .cfi_startproc"));
    }

  unwind->personality_index = -1;
  unwind->personality_routine = NULL;
  unwind->table_entry = NULL;
  unwind->data_bytes = -1;
}

static void
tic6x_output_exidx_entry (void)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();
  const segT old_seg = now_seg;
  const subsegT old_subseg = now_subseg;

  tic6x_start_unwind_section (unwind->saved_seg, 1);
  frag_align (2, 0, 0);
  record_alignment (now_seg, 2);

  char *ptr = frag_more (8);
  memset (ptr, 0, 8);
  const long where = frag_now_fix () - 8;

  fix_new (frag_now, where, 4, unwind->function_start, 0, 1,
	   BFD_RELOC_C6000_PREL31);

  static const char *const personality_names[] = {
    "__c6xabi_unwind_cpp_pr0", "__c6xabi_unwind_cpp_pr1",
    "__c6xabi_unwind_cpp_pr2", "__c6xabi_unwind_cpp_pr3",
    "__c6xabi_unwind_cpp_pr4"
  };
  const size_t num_personality_routines =
    sizeof (personality_names) / sizeof (personality_names[0]);

  if (unwind->personality_index >= 0
      && (size_t) unwind->personality_index < num_personality_routines)
    {
      const unsigned int personality_bit = 1 << unwind->personality_index;
      unsigned int *marked_dependency_ptr =
        &seg_info (now_seg)->tc_segment_info_data.marked_pr_dependency;

      if (!(*marked_dependency_ptr & personality_bit))
        {
          symbolS *pr_symbol =
            symbol_find_or_make (personality_names[unwind->personality_index]);
          fix_new (frag_now, where, 0, pr_symbol, 0, 1, BFD_RELOC_NONE);
          *marked_dependency_ptr |= personality_bit;
        }
    }

  if (unwind->table_entry)
    {
      fix_new (frag_now, where + 4, 4, unwind->table_entry, 0, 1,
	       BFD_RELOC_C6000_PREL31);
    }
  else
    {
      md_number_to_chars (ptr + 4, unwind->data, 4);
    }

  subseg_set (old_seg, old_subseg);
}

static bool
is_compact_personality (int index)
{
  return index == 3 || index == 4;
}

static bool
generate_compact_unwind_data (tic6x_unwind_info * unwind)
{
  offsetT cfa_offset = unwind->cfa_offset;
  unsigned safe_mask = unwind->safe_mask;
  unsigned compact_mask = unwind->compact_mask;

  if (cfa_offset >= MAX_COMPACT_SP_OFFSET)
    {
      as_bad (_("stack pointer offset too large for personality routine"));
      return false;
    }
  if (unwind->reg_saved_mask
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
    unwind->data |= cfa_offset << (17 - 3);

  if (unwind->personality_index == 3)
    unwind->data |= safe_mask << 4;
  else
    unwind->data |= compact_mask << 4;

  unwind->data |= unwind->return_reg;
  unwind->data_bytes = 4;
  return true;
}

static void
emit_cfa_opcodes (tic6x_unwind_info * unwind)
{
  offsetT cfa_offset = unwind->cfa_offset;

  if (unwind->cfa_reg == 15)
    {
      tic6x_unwind_byte (UNWIND_OP_MV_FP);
      return;
    }

  if (cfa_offset == 0)
    return;

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

static void
emit_generic_pop_reg_opcodes (tic6x_unwind_info * unwind)
{
  unsigned int regs_to_pop = unwind->saved_reg_count;
  int last_val = 0;
  bool second_nibble = false;

  tic6x_unwind_byte (UNWIND_OP_POP_REG | unwind->saved_reg_count);

  for (offsetT cur_offset = 0; regs_to_pop > 0; cur_offset -= 4)
    {
      int val = 0xf;
      for (int reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
	{
	  if (unwind->reg_saved[reg] && unwind->reg_offset[reg] == cur_offset)
	    {
	      val = reg;
	      regs_to_pop--;
	      break;
	    }
	}

      if (second_nibble)
	tic6x_unwind_byte ((last_val << 4) | val);
      else
	last_val = val;

      second_nibble = !second_nibble;
    }

  if (second_nibble)
    tic6x_unwind_byte ((last_val << 4) | 0xf);
}

static void
emit_pop_opcodes (tic6x_unwind_info * unwind)
{
  if (unwind->safe_mask)
    tic6x_unwind_2byte (UNWIND_OP2_POP | unwind->safe_mask);
  else if (unwind->pop_rts)
    tic6x_unwind_byte (UNWIND_OP_POP_RTS);
  else if (unwind->compact_mask)
    tic6x_unwind_2byte (UNWIND_OP2_POP_COMPACT | unwind->compact_mask);
  else if (unwind->reg_saved_mask)
    emit_generic_pop_reg_opcodes (unwind);
}

static void
generate_generic_unwind_opcodes (tic6x_unwind_info * unwind)
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

  if (unwind->return_reg != UNWIND_B3)
    tic6x_unwind_byte (UNWIND_OP_RET | unwind->return_reg);

  emit_cfa_opcodes (unwind);
  emit_pop_opcodes (unwind);

  while ((unwind->data_bytes & 3) != 0)
    tic6x_unwind_byte (UNWIND_OP_RET | UNWIND_B3);

  if (unwind->personality_index == -1
      && unwind->personality_routine == NULL)
    unwind->personality_index = 0;
}

static void
auto_select_personality (tic6x_unwind_info * unwind)
{
  if (unwind->personality_index != -1 || unwind->personality_routine != NULL)
    return;

  if (unwind->reg_saved_mask
      || unwind->cfa_offset >= MAX_COMPACT_SP_OFFSET)
    unwind->personality_index = -1;
  else if (unwind->safe_mask)
    unwind->personality_index = 3;
  else
    unwind->personality_index = 4;
}

static void
handle_extab_creation (tic6x_unwind_info * unwind, bool need_extab)
{
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
}

static void
fill_bytecode_length (tic6x_unwind_info * unwind)
{
  if (!unwind->table_entry)
    return;

  if (unwind->data_bytes > 0x400)
    {
      as_bad (_("too many unwinding instructions"));
      return;
    }

  valueT tmp;
  if (unwind->personality_index == -1)
    {
      tmp = md_chars_to_number (unwind->frag_start + 4, 4);
      tmp |= (valueT) ((unwind->data_bytes - 8) >> 2) << 24;
      md_number_to_chars (unwind->frag_start + 4, tmp, 4);
    }
  else if (unwind->personality_index == 1
	   || unwind->personality_index == 2)
    {
      tmp = md_chars_to_number (unwind->frag_start, 4);
      tmp |= ((unwind->data_bytes - 4) >> 2) << 16;
      md_number_to_chars (unwind->frag_start, tmp, 4);
    }
}

static void
tic6x_output_unwinding (bool need_extab)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();

  if (unwind->personality_index == -2)
    {
      unwind->data = 1;
      tic6x_output_exidx_entry ();
      return;
    }

  auto_select_personality (unwind);

  unwind->table_entry = NULL;
  if (is_compact_personality (unwind->personality_index))
    {
      if (!generate_compact_unwind_data (unwind))
	return;
    }
  else
    {
      generate_generic_unwind_opcodes (unwind);
    }

  handle_extab_creation (unwind, need_extab);
  fill_bytecode_length (unwind);

  tic6x_output_exidx_entry ();
}

/* FIXME: This will get horribly confused if cfi directives are emitted for
   function epilogue.  */
void
tic6x_cfi_endproc (struct fde_entry *fde)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();
  offsetT cfa_offset = 0;
  unsigned safe_mask = 0;
  unsigned compact_mask = 0;
  unsigned reg_saved_mask = 0;

  unwind->cfa_reg = 31;
  unwind->return_reg = UNWIND_B3;
  unwind->saved_reg_count = 0;
  unwind->pop_rts = false;
  unwind->saved_seg = now_seg;
  unwind->saved_subseg = now_subseg;

  for (int reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
    unwind->reg_saved[reg] = false;

  for (struct cfi_insn_data *insn = fde->data; insn; insn = insn->next)
    {
      switch (insn->insn)
	{
	case DW_CFA_advance_loc:
	  break;

	case DW_CFA_def_cfa:
	  unwind->cfa_reg = insn->u.ri.reg;
	  cfa_offset = insn->u.ri.offset;
	  break;

	case DW_CFA_def_cfa_register:
	  unwind->cfa_reg = insn->u.r;
	  break;

	case DW_CFA_def_cfa_offset:
	  cfa_offset = insn->u.i;
	  break;

	case DW_CFA_undefined:
	case DW_CFA_same_value:
	  {
	    int reg = tic6x_unwind_reg_from_dwarf (insn->u.r);
	    if (reg >= 0)
	      unwind->reg_saved[reg] = false;
	  }
	  break;

	case DW_CFA_offset:
	  {
	    int reg = tic6x_unwind_reg_from_dwarf (insn->u.ri.reg);
	    if (reg < 0)
	      {
		as_bad (_("unable to generate unwinding opcode for reg %d"),
			insn->u.ri.reg);
		return;
	      }
	    unwind->reg_saved[reg] = true;
	    unwind->reg_offset[reg] = insn->u.ri.offset;
	    if (insn->u.ri.reg == UNWIND_B3)
	      unwind->return_reg = UNWIND_B3;
	  }
	  break;

	case DW_CFA_register:
	  if (insn->u.rr.reg1 != 19)
	    {
	      as_bad (_("unable to generate unwinding opcode for reg %d"),
		      insn->u.rr.reg1);
	      return;
	    }
	  {
	    int reg = tic6x_unwind_reg_from_dwarf (insn->u.rr.reg2);
	    if (reg < 0)
	      {
		as_bad (_("unable to generate unwinding opcode for reg %d"),
			insn->u.rr.reg2);
		return;
	      }
	    unwind->return_reg = reg;
	    unwind->reg_saved[UNWIND_B3] = false;
	    if (unwind->reg_saved[reg])
	      {
		as_bad (_("unable to restore return address from "
			  "previously restored reg"));
		return;
	      }
	  }
	  break;

	case DW_CFA_restore:
	case DW_CFA_remember_state:
	case DW_CFA_restore_state:
	case DW_CFA_GNU_window_save:
	case CFI_escape:
	case CFI_val_encoded_addr:
	  as_bad (_("unhandled CFA insn for unwinding (%d)"), insn->insn);
	  return;

	default:
	  as_bad (_("unhandled CFA insn for unwinding (%d)"), insn->insn);
	  return;
	}
    }

  if (unwind->cfa_reg != 15 && unwind->cfa_reg != 31)
    {
      as_bad (_("unable to generate unwinding opcode for frame pointer reg %d"),
	      unwind->cfa_reg);
      return;
    }

  if (unwind->cfa_reg == 15)
    {
      if (cfa_offset != 0)
	{
	  as_bad (_("unable to generate unwinding opcode for "
		    "frame pointer offset"));
	  return;
	}
    }
  else if ((cfa_offset & 7) != 0)
    {
      as_bad (_("unwound stack pointer not doubleword aligned"));
      return;
    }

  for (int reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
    {
      if (unwind->reg_saved[reg])
	reg_saved_mask |= 1 << (TIC6X_NUM_UNWIND_REGS - (reg + 1));
    }

  if (reg_saved_mask)
    {
      bool is_safe_frame = true;
      offsetT save_offset = 0;
      for (int reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
	{
	  if (!unwind->reg_saved[reg])
	    continue;

	  bool is_swapped_pair =
	    target_big_endian && reg < TIC6X_NUM_UNWIND_REGS - 1
	    && unwind->reg_saved[reg + 1]
	    && (tic6x_unwind_frame_regs[reg] ==
		tic6x_unwind_frame_regs[reg + 1] + 1)
	    && (tic6x_unwind_frame_regs[reg] & 1) == 1 && (save_offset & 4) == 4;

	  if (is_swapped_pair)
	    {
	      if (save_offset != unwind->reg_offset[reg + 1]
		  || save_offset - 4 != unwind->reg_offset[reg])
		{
		  is_safe_frame = false;
		  break;
		}
	      save_offset -= 8;
	      reg++;
	    }
	  else
	    {
	      if (save_offset != unwind->reg_offset[reg])
		{
		  is_safe_frame = false;
		  break;
		}
	      save_offset -= 4;
	    }
	}
      if (is_safe_frame)
	{
	  safe_mask = reg_saved_mask;
	  reg_saved_mask = 0;
	}
    }

  if (reg_saved_mask)
    {
      bool is_compact_frame = true;
      offsetT save_offset = 0;
      for (int reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
	{
	  if (!unwind->reg_saved[reg])
	    continue;

	  bool is_paired_reg =
	    reg < TIC6X_NUM_UNWIND_REGS - 1 && unwind->reg_saved[reg + 1]
	    && (tic6x_unwind_frame_regs[reg] ==
		tic6x_unwind_frame_regs[reg + 1] + 1)
	    && (tic6x_unwind_frame_regs[reg + 1] & 1) == 0 && save_offset != 0;

	  if (is_paired_reg)
	    {
	      int high_offset = target_big_endian ? 4 : 0;
	      if (save_offset + 4 - high_offset != unwind->reg_offset[reg]
		  || save_offset + high_offset != unwind->reg_offset[reg + 1])
		{
		  is_compact_frame = false;
		  break;
		}
	      reg++;
	    }
	  else
	    {
	      if (save_offset != unwind->reg_offset[reg])
		{
		  is_compact_frame = false;
		  break;
		}
	    }
	  save_offset -= 8;
	}

      if (is_compact_frame)
	{
	  compact_mask = reg_saved_mask;
	  reg_saved_mask = 0;
	}
    }

  if (reg_saved_mask == 0x17ff)
    {
      const int *pop_rts_offset = target_big_endian
				    ? tic6x_pop_rts_offset_big
				    : tic6x_pop_rts_offset_little;
      bool is_pop_rts = true;
      for (int reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
	{
	  if (reg == UNWIND_B15)
	    continue;

	  if (unwind->reg_offset[reg] != pop_rts_offset[reg] * 4)
	    {
	      is_pop_rts = false;
	      break;
	    }
	}

      if (is_pop_rts)
	{
	  unwind->pop_rts = true;
	  reg_saved_mask = 0;
	}
    }

  offsetT final_save_offset = 0;
  if (reg_saved_mask)
    {
      for (int reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
	{
	  if (!unwind->reg_saved[reg])
	    continue;

	  unwind->saved_reg_count++;
	  if (unwind->reg_offset[reg] > 0 || unwind->reg_offset[reg] < -0x800
	      || (unwind->reg_offset[reg] & 3) != 0)
	    {
	      as_bad (_("stack frame layout too complex for unwinder"));
	      return;
	    }

	  if (unwind->reg_offset[reg] < final_save_offset)
	    final_save_offset = unwind->reg_offset[reg] - 4;
	}
    }

  final_save_offset &= ~7;

  if (unwind->cfa_reg == 31 && !reg_saved_mask)
    {
      cfa_offset += final_save_offset;
      if (cfa_offset < 0)
	{
	  as_bad (_("unwound frame has negative size"));
	  return;
	}
    }

  unwind->safe_mask = safe_mask;
  unwind->compact_mask = compact_mask;
  unwind->reg_saved_mask = reg_saved_mask;
  unwind->cfa_offset = cfa_offset;
  unwind->function_start = fde->start_address;
}
