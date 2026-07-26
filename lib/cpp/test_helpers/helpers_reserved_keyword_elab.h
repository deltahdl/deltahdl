#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <initializer_list>
#include <iterator>
#include <string>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_keyword_sweep_skips.h"
#include "helpers_keyword_version.h"
#include "helpers_rtlir_lookup.h"
#include "model_keyword_table_sweeps.h"
#include "model_keyword_tables.h"

using namespace delta;

// §22.14: a version_specifier puts one reserved word list in force, and each
// list includes the lists of the versions before it. The checks here carry the
// reserving half of that -- a listed word cannot name anything the elaborator
// builds, while under a specifier whose list leaves it free the same
// declaration reaches the design. Pairing the two legs is the whole claim: a
// rejection on its own could come from anything, and it is the acceptance
// under the earlier specifier that pins the rejection on the word being
// reserved.
//
// Every check takes the specifier as its parameter, because that is the only
// thing that varies between one version's statement of a rule and the next's.

// Every entry of `t` put in an identifier slot and rejected under `spec`, and
// -- where an earlier specifier leaves the entry free -- the same declaration
// elaborating there into a variable of the width it asked for. Reading the
// variable back is what keeps the accepting leg from being any elaboration
// that happens to succeed.
inline void ExpectKeywordTableIsReserved(const char* spec,
                                         const KeywordTableSweep& t) {
  EXPECT_EQ(t.count, t.expected_count) << t.what;
  size_t swept = 0;
  for (size_t i = 0; i < t.count; ++i) {
    const char* word = t.words[i];
    if (t.skip != nullptr && t.skip(word)) continue;
    ++swept;

    ElabFixture reserved;
    ElaborateWithPreprocessor(In(spec, VarDecl(word)), reserved, "m");
    EXPECT_TRUE(reserved.has_errors)
        << word << " is listed in " << t.what << " and is reserved here";

    for (const char* earlier : t.earlier) {
      if (earlier == nullptr) continue;
      ElabFixture freed;
      auto* design =
          ElaborateWithPreprocessor(In(earlier, VarDecl(word)), freed, "m");
      ASSERT_NE(design, nullptr)
          << t.what << ' ' << word << " under " << earlier;
      EXPECT_FALSE(freed.has_errors) << t.what << ' ' << word;
      const auto* v = FindVar(design, "m", word);
      ASSERT_NE(v, nullptr) << t.what << ' ' << word;
      EXPECT_EQ(v->width, 8u) << t.what << ' ' << word;
    }
  }
  EXPECT_EQ(swept, t.expected_swept) << t.what;
}

// The ten words on which the two lists published for the same Verilog standard
// disagree: each names a variable under the companion list that drops them,
// which is what shows a version that inherits "1364-2001" inherits the full
// list rather than the shorter one.
inline void ExpectConfigurationWordsNameVariablesUnderNoconfig() {
  EXPECT_EQ(std::size(kConfigurationWords), 10u);
  for (const char* word : kConfigurationWords) {
    ElabFixture dropped;
    auto* design =
        ElaborateWithPreprocessor(InNoconfig(VarDecl(word)), dropped, "m");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(dropped.has_errors) << word;
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;
  }
}

// Words no list in force reserves, checked from both sides. Each names an
// object that really reaches the design, and none of them is a data type --
// the half that would go unchecked if only the naming side were tested. When
// `later_spec` is given, the same declaration is rejected there, which is what
// makes the word a *later* one rather than one the implementation simply does
// not know.
//
// None of the words a caller passes here opens a design element, so putting
// one at the head of a line leaves the region machinery -- which tracks design
// elements by a line's first word, without regard to the list in force -- out
// of the picture, and the only thing that can reject the source is the word
// not being a type.
inline void ExpectWordsNameObjectsButAreNotTypes(
    const char* spec, std::initializer_list<const char*> words,
    const char* later_spec = nullptr) {
  for (const char* word : words) {
    ElabFixture named;
    auto* design =
        ElaborateWithPreprocessor(In(spec, VarDecl(word)), named, "m");
    ASSERT_NE(design, nullptr) << word;
    EXPECT_FALSE(named.has_errors) << word;
    const auto* v = FindVar(design, "m", word);
    ASSERT_NE(v, nullptr) << word;
    EXPECT_EQ(v->width, 8u) << word;

    ElabFixture as_type;
    ElaborateWithPreprocessor(In(spec, std::string("module m;\n  ") + word +
                                           " [7:0] v;\nendmodule\n"),
                              as_type, "m");
    EXPECT_TRUE(as_type.has_errors)
        << word << " is not a data type under this version";

    if (later_spec == nullptr) continue;
    ElabFixture later;
    ElaborateWithPreprocessor(In(later_spec, VarDecl(word)), later, "m");
    EXPECT_TRUE(later.has_errors) << word << " is reserved by " << later_spec;
  }
}

// Declarations rejected inside a `begin_keywords region for `spec` and
// elaborating outside one. The second leg is what shows the region -- and not
// some unrelated limitation -- is doing the rejecting.
inline void ExpectDeclsFailInRegionButElaborateOutside(
    const char* spec, std::initializer_list<const char*> decls) {
  for (const char* decl : decls) {
    std::string src = std::string("module t;\n  ") + decl + "\nendmodule\n";

    ElabFixture in_region;
    ElaborateWithPreprocessor(In(spec, src), in_region, "t");
    EXPECT_TRUE(in_region.has_errors) << decl;

    ElabFixture outside;
    auto* design = ElaborateWithPreprocessor(src, outside, "t");
    ASSERT_NE(design, nullptr) << decl;
    EXPECT_FALSE(outside.has_errors) << decl;
  }
}

// Words a later standard reserves, staying ordinary identifiers all the way
// into the elaborated design: each names a variable that really exists there,
// carrying the storage its declaration asked for. Getting past the parser is
// not enough -- the design is what the rest of the tool works from.
inline void ExpectFreedWordsNameElaboratedVariables(const char* spec) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In(spec,
                                              "module m;\n"
                                              "  reg [63:0] logic;\n"
                                              "  reg [7:0]  bit;\n"
                                              "  integer    int;\n"
                                              "  real       shortreal;\n"
                                              "  time       longint;\n"
                                              "  event      package;\n"
                                              "endmodule\n"),
                                           f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* v = FindVar(design, "m", "logic");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 64u);

  v = FindVar(design, "m", "bit");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 8u);

  v = FindVar(design, "m", "int");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 32u);

  v = FindVar(design, "m", "shortreal");
  ASSERT_NE(v, nullptr);
  EXPECT_TRUE(v->is_real);

  v = FindVar(design, "m", "longint");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 64u);

  v = FindVar(design, "m", "package");
  ASSERT_NE(v, nullptr);
  EXPECT_TRUE(v->is_event);
}

// The four names a two-module hierarchy is built from. A word free under one
// specifier has to fill each of them, so a test names all four rather than
// only the declaration slot.
struct FreedHierarchyNames {
  const char* design_element;
  const char* input_port;
  const char* output_port;
  const char* instance;
};

// A word free under `spec` naming the design element itself, its ports, and
// the instance that binds to it -- the region governs a whole elaborated
// hierarchy, not one declaration inside one module.
inline void ExpectFreedWordsNameModulePortsAndInstance(
    const char* spec, const FreedHierarchyNames& names) {
  const std::string child_name = names.design_element;
  const std::string in_name = names.input_port;
  const std::string out_name = names.output_port;

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      In(spec, "module " + child_name + " (input wire " + in_name +
                   ",\n            output wire " + out_name + ");\n" +
                   "  assign " + out_name + " = " + in_name +
                   ";\n"
                   "endmodule\n"
                   "module top;\n"
                   "  wire a, b;\n"
                   "  " +
                   child_name + " " + names.instance + " (." + in_name +
                   "(a), ." + out_name + "(b));\n" + "endmodule\n"),
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* child = FindModule(design, child_name);
  ASSERT_NE(child, nullptr);
  ASSERT_EQ(child->ports.size(), 2u);
  EXPECT_EQ(child->ports[0].name, in_name);
  EXPECT_EQ(child->ports[0].direction, Direction::kInput);
  EXPECT_EQ(child->ports[1].name, out_name);
  EXPECT_EQ(child->ports[1].direction, Direction::kOutput);

  const auto* top = FindModule(design, "top");
  ASSERT_NE(top, nullptr);
  bool found_instance = false;
  for (const auto& inst : top->children) {
    if (inst.inst_name == names.instance && inst.module_name == child_name) {
      found_instance = true;
    }
  }
  EXPECT_TRUE(found_instance);
}

// The constant forms that reach a declaration's width, which is where a
// constant expression is actually required: a literal, a `parameter`, a
// `localparam`, and a call to an `automatic` function that is folded. All four
// have to arrive at the same width, and the two named constants are read back
// so the overridable and the local form are told apart. `param_type` and
// `localparam_type` type the two constants, and are empty for a version whose
// list carries no data type word to put there.
//
// The remaining constant form, a genvar, shows its value in the copies its
// loop produces rather than in a width, and Table 22-2's declaration check
// observes it doing exactly that.
inline void ExpectEveryConstantFormResolves(const char* spec,
                                            const char* param_type,
                                            const char* localparam_type) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      In(spec, std::string("module t;\n") + "  parameter  " + param_type +
                   " P = 8;\n" + "  localparam " + localparam_type +
                   " L = 8;\n"
                   "  function automatic int width_of(input int n);\n"
                   "    width_of = n;\n"
                   "  endfunction\n"
                   "  logic [7:0]             from_literal;\n"
                   "  logic [P-1:0]           from_parameter;\n"
                   "  logic [L-1:0]           from_localparam;\n"
                   "  logic [width_of(8)-1:0] from_function;\n"
                   "endmodule\n"),
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* p = FindParam(design, "t", "P");
  ASSERT_NE(p, nullptr);
  EXPECT_FALSE(p->is_localparam);
  EXPECT_EQ(p->resolved_value, 8);
  const auto* l = FindParam(design, "t", "L");
  ASSERT_NE(l, nullptr);
  EXPECT_TRUE(l->is_localparam);
  EXPECT_EQ(l->resolved_value, 8);

  const char* kNames[] = {"from_literal", "from_parameter", "from_localparam",
                          "from_function"};
  for (const char* name : kNames) {
    const auto* v = FindVar(design, "t", name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->width, 8u) << name;
  }
}

// The declaration forms a word sweep does not reach, carried into the
// elaborated design. A declaration may bring its own initializer along, a port
// may be typed in the module header, and a port may instead be typed in the
// body in the separate style where the header lists only names. Each is a
// production of its own, and they are exercised across a hierarchy rather than
// inside one module, so a port's type has to survive the binding as well as
// the declaration.
inline void ExpectEveryDeclarationFormElaborates(const char* spec) {
  ElabFixture ansi;
  auto* design = ElaborateWithPreprocessor(
      In(spec,
         "module child (input logic [7:0] a, input byte b,\n"
         "              output int y);\n"
         "  assign y = a + b;\n"
         "endmodule\n"
         "module top;\n"
         "  logic [7:0] src;\n"
         "  byte        step;\n"
         "  int         dst;\n"
         "  int         counted = 21;\n"
         "  child u1 (.a(src), .b(step), .y(dst));\n"
         "endmodule\n"),
      ansi, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(ansi.has_errors);

  const auto* child = FindModule(design, "child");
  ASSERT_NE(child, nullptr);
  ASSERT_EQ(child->ports.size(), 3u);
  EXPECT_EQ(child->ports[0].type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(child->ports[0].width, 8u);
  EXPECT_EQ(child->ports[1].type_kind, DataTypeKind::kByte);
  EXPECT_EQ(child->ports[1].width, 8u);
  EXPECT_EQ(child->ports[2].type_kind, DataTypeKind::kInt);
  EXPECT_EQ(child->ports[2].direction, Direction::kOutput);
  EXPECT_EQ(child->ports[2].width, 32u);

  // The parent's own objects, including the one whose declaration carries its
  // value rather than taking it from a separate assignment.
  const auto* dst = FindVar(design, "top", "dst");
  ASSERT_NE(dst, nullptr);
  EXPECT_EQ(dst->width, 32u);
  const auto* counted = FindVar(design, "top", "counted");
  ASSERT_NE(counted, nullptr);
  EXPECT_EQ(counted->width, 32u);
  EXPECT_NE(counted->init_expr, nullptr);

  ElabFixture non_ansi;
  design = ElaborateWithPreprocessor(In(spec,
                                        "module ch (a, y);\n"
                                        "  input  [7:0] a;\n"
                                        "  output [7:0] y;\n"
                                        "  logic  [7:0] y;\n"
                                        "  always_comb y = a + a;\n"
                                        "endmodule\n"),
                                     non_ansi, "ch");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(non_ansi.has_errors);
  const auto* m = FindModule(design, "ch");
  ASSERT_NE(m, nullptr);
  ASSERT_EQ(m->ports.size(), 2u);
  EXPECT_EQ(m->ports[1].name, "y");
  EXPECT_EQ(m->ports[1].direction, Direction::kOutput);
  const auto* y = FindVar(design, "ch", "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->width, 8u);
}
