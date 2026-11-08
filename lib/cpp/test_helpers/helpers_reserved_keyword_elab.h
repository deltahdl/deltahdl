#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <initializer_list>
#include <iterator>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_keyword_version.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "model_keyword_table_sweeps.h"
#include "model_keyword_tables.h"
#include "parser/ast_type.h"

using namespace delta;

inline void ExpectKeywordTableIsReserved(const char* spec,
                                         const KeywordTableSweep& t) {
  EXPECT_EQ(t.count, t.expected_count) << t.what;
  size_t swept = 0;
  for (size_t i = 0; i < t.count; ++i) {
    const char* word = t.words[i];
    if (t.skip != nullptr && t.skip(word)) continue;
    ++swept;

    ElabFixture reserved;
    ElaborateWithPreprocessorAllowingParseErrors(In(spec, VarDecl(word)),
                                                 reserved, "m");
    EXPECT_TRUE(
        ReportedError(reserved.diag.Diagnostics(),
                      std::string("expected identifier, got '") + word + "'",
                      LineInRegion(2), "6.8"))
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
    ElaborateWithPreprocessorAllowingParseErrors(
        In(spec,
           std::string("module m;\n  ") + word + " [7:0] v;\nendmodule\n"),
        as_type, "m");
    EXPECT_TRUE(ReportedError(as_type.diag.Diagnostics(),
                              "expected ';', got '['", LineInRegion(2), "6.8"))
        << word << " is not a data type under this version";

    if (later_spec == nullptr) continue;
    ElabFixture later;
    ElaborateWithPreprocessorAllowingParseErrors(In(later_spec, VarDecl(word)),
                                                 later, "m");
    EXPECT_TRUE(
        ReportedError(later.diag.Diagnostics(),
                      std::string("expected identifier, got '") + word + "'",
                      LineInRegion(2), "6.8"))
        << word << " is reserved by " << later_spec;
  }
}

inline void ExpectDeclsFailInRegionButElaborateOutside(
    const char* spec, std::initializer_list<const char*> decls) {
  for (const char* decl : decls) {
    std::string src = std::string("module t;\n  ") + decl + "\nendmodule\n";

    ElabFixture in_region;
    ElaborateWithPreprocessorAllowingParseErrors(In(spec, src), in_region, "t");
    const bool kHasPackedDim =
        std::string_view(decl).find('[') != std::string_view::npos;
    std::string message = "expected ';', got '['";
    const char* subclause = "6.8";
    if (!kHasPackedDim) {
      std::string_view head_word(decl);
      head_word = head_word.substr(0, head_word.find(' '));
      message = "declaration of type '" + std::string(head_word) +
                "' does not precede";
      subclause = "6.18";
    }
    EXPECT_TRUE(ReportedError(in_region.diag.Diagnostics(), message,
                              LineInRegion(2), subclause))
        << decl;

    ElabFixture outside;
    auto* design = ElaborateWithPreprocessor(src, outside, "t");
    ASSERT_NE(design, nullptr) << decl;
    EXPECT_FALSE(outside.has_errors) << decl;
  }
}

inline void ExpectFreedWordsNameVariablesOfDeclaredWidth(RtlirDesign* design) {
  const auto* v = FindVar(design, "m", "logic");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 64u);

  v = FindVar(design, "m", "bit");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 8u);

  v = FindVar(design, "m", "int");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 32u);

  v = FindVar(design, "m", "longint");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 64u);
}

inline void ExpectFreedWordsNameRealAndEventVariables(RtlirDesign* design) {
  const auto* v = FindVar(design, "m", "shortreal");
  ASSERT_NE(v, nullptr);
  EXPECT_TRUE(v->is_real);

  v = FindVar(design, "m", "package");
  ASSERT_NE(v, nullptr);
  EXPECT_TRUE(v->is_event);
}

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

  ExpectFreedWordsNameVariablesOfDeclaredWidth(design);
  ExpectFreedWordsNameRealAndEventVariables(design);
}

struct FreedHierarchyNames {
  const char* design_element;
  const char* input_port;
  const char* output_port;
  const char* instance;
};

inline void ExpectFreedWordsNameModulePortsAndInstance(
    const char* spec, const FreedHierarchyNames& names) {
  const std::string kChildName = names.design_element;
  const std::string kInName = names.input_port;
  const std::string kOutName = names.output_port;

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      In(spec, "module " + kChildName + " (input wire " + kInName +
                   ",\n            output wire " + kOutName + ");\n" +
                   "  assign " + kOutName + " = " + kInName +
                   ";\n"
                   "endmodule\n"
                   "module top;\n"
                   "  wire a, b;\n"
                   "  " +
                   kChildName + " " + names.instance + " (." + kInName +
                   "(a), ." + kOutName + "(b));\n" + "endmodule\n"),
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* child = FindModule(design, kChildName);
  ASSERT_NE(child, nullptr);
  ASSERT_EQ(child->ports.size(), 2u);
  EXPECT_EQ(child->ports[0].name, kInName);
  EXPECT_EQ(child->ports[0].direction, Direction::kInput);
  EXPECT_EQ(child->ports[1].name, kOutName);
  EXPECT_EQ(child->ports[1].direction, Direction::kOutput);

  const auto* top = FindModule(design, "top");
  ASSERT_NE(top, nullptr);
  bool found_instance = false;
  for (const auto& inst : top->children) {
    if (inst.inst_name == names.instance && inst.module_name == kChildName) {
      found_instance = true;
    }
  }
  EXPECT_TRUE(found_instance);
}

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

  constexpr const char* kNames[] = {"from_literal", "from_parameter",
                                    "from_localparam", "from_function"};
  for (const char* name : kNames) {
    const auto* v = FindVar(design, "t", name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->width, 8u) << name;
  }
}

inline void ExpectAnsiHeaderPortsCarryDeclaredTypes(RtlirDesign* design) {
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
}

inline void ExpectParentObjectsAndInitializerElaborate(RtlirDesign* design) {
  const auto* dst = FindVar(design, "top", "dst");
  ASSERT_NE(dst, nullptr);
  EXPECT_EQ(dst->width, 32u);
  const auto* counted = FindVar(design, "top", "counted");
  ASSERT_NE(counted, nullptr);
  EXPECT_EQ(counted->width, 32u);
  EXPECT_NE(counted->init_expr, nullptr);
}

inline void ExpectNonAnsiPortDeclarationsElaborate(const char* spec) {
  ElabFixture non_ansi;
  auto* design = ElaborateWithPreprocessor(In(spec,
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

inline void ExpectEveryDeclarationFormElaborates(const char* spec) {
  ElabFixture ansi;
  auto* design = ElaborateWithPreprocessor(
      In(spec,
         "module child (input logic [7:0] a, input var byte b,\n"
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

  ExpectAnsiHeaderPortsCarryDeclaredTypes(design);
  ExpectParentObjectsAndInitializerElaborate(design);
  ExpectNonAnsiPortDeclarationsElaborate(spec);
}
