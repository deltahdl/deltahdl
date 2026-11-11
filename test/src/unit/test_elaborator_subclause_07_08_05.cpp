#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <format>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(UserDefinedTypeAssocArrayElaboration, AssocArrayRealIndex_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[real];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal type shall not be used as an "
                            "associative array index type",
                            2, "7.8.5"));
}

TEST(UserDefinedTypeAssocArrayElaboration, AssocArrayShortrealIndex_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[shortreal];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal type shall not be used as an "
                            "associative array index type",
                            2, "7.8.5"));
}

TEST(UserDefinedTypeAssocArrayElaboration, EnumTypedefIndexAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  int aa[color_t];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "aa") {
      EXPECT_TRUE(v.is_assoc);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(UserDefinedTypeAssocArrayElaboration,
     StructIndexWithDynamicMemberAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef struct {byte B; int I[*];} unpkt_t;\n"
      "  int aa[unpkt_t];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "aa") {
      EXPECT_TRUE(v.is_assoc);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(UserDefinedTypeAssocArrayElaboration, StructIndexContainingRealRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct {real r; int i;} mixed_t;\n"
      "  int aa[mixed_t];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal type shall not be used as an "
                            "associative array index type",
                            3, "7.8.5"));
}

TEST(UserDefinedTypeAssocArrayElaboration,
     TypedefResolvingToRealIndexRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef real real_alias_t;\n"
      "  int aa[real_alias_t];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal type shall not be used as an "
                            "associative array index type",
                            3, "7.8.5"));
}

TEST(UserDefinedTypeAssocArrayElaboration,
     StructMemberTypedefResolvingToRealRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef real real_alias_t;\n"
      "  typedef struct {real_alias_t r; int i;} mixed_t;\n"
      "  int aa[mixed_t];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal type shall not be used as an "
                            "associative array index type",
                            4, "7.8.5"));
}

TEST(UserDefinedTypeAssocArrayElaboration,
     StructWithNestedTypedefStructContainingRealRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct {real r;} inner_t;\n"
      "  typedef struct {inner_t x; int i;} outer_t;\n"
      "  int aa[outer_t];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal type shall not be used as an "
                            "associative array index type",
                            4, "7.8.5"));
}

TEST(UserDefinedTypeAssocArrayElaboration,
     StructWithInlineNestedStructContainingRealRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct {struct {real r;} x; int i;} outer_t;\n"
      "  int aa[outer_t];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal type shall not be used as an "
                            "associative array index type",
                            3, "7.8.5"));
}

std::string TwoPackagesRealHolderIndex(std::string_view imported,
                                       std::string_view typedef_line) {
  return "package q;\n"
         "  typedef struct { real r; } real_holder_t;\n"
         "endpackage\n"
         "package r;\n"
         "  typedef struct { int r; } real_holder_t;\n"
         "endpackage\n"
         "module top;\n"
         "  import " +
         std::string(imported) + "::*;\n  " + std::string(typedef_line) +
         "\n"
         "  int aa[idx_t];\n"
         "endmodule\n";
}

TEST(UserDefinedTypeAssocArrayElaboration,
     StructMemberQualifiedByAnotherPackageHoldingRealRejected) {
  ElabFixture f;
  ElaborateSrc(TwoPackagesRealHolderIndex(
                   "r", "typedef struct { q::real_holder_t h; int i; } idx_t;"),
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal type shall not be used as an "
                            "associative array index type",
                            10, "7.8.5"));
}

TEST(UserDefinedTypeAssocArrayElaboration,
     StructMemberQualifiedByRealFreePackageAllowedDespiteImportedReal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      TwoPackagesRealHolderIndex(
          "q", "typedef struct { r::real_holder_t h; int i; } idx_t;"),
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UserDefinedTypeAssocArrayElaboration,
     TypedefOfQualifiedRealFreeTypeAllowedDespiteImportedReal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      TwoPackagesRealHolderIndex("q", "typedef r::real_holder_t idx_t;"), f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssocIndexTypeValidation, RealIndexTypeOnAnyDimensionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct { real r; } rs_t;\n"
      "  int a [real];\n"
      "  int b [2][real];\n"
      "  int c [int][rs_t];\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line = 3; line <= 5; ++line) {
    EXPECT_TRUE(ReportedError(diags,
                              "real or shortreal type shall not be used as an "
                              "associative array index type",
                              line, "7.8.5"));
  }
}

TEST(AssocIndexTypeValidation, RealIndexTypeRejectedInEveryScope) {
  ElabFixture f;
  ElaborateSrc(
      "typedef int t_real_idx [real];\n"
      "package p; int pa [real]; endpackage\n"
      "module top;\n"
      "  class C; int ca [real]; endclass\n"
      "  function void f(int fa [real]); endfunction\n"
      "  initial begin\n"
      "    int la [real];\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const uint32_t kLines[] = {1, 2, 4, 5, 7};
  for (uint32_t line : kLines) {
    EXPECT_TRUE(ReportedError(diags,
                              "real or shortreal type shall not be used as an "
                              "associative array index type",
                              line, "7.8.5"));
  }
}

TEST(UserDefinedTypeAssocArrayElaboration, ScopedTypeNameIndexIsAssociative) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef bit [3:0] idx_t;\n"
      "  parameter int N = 4;\n"
      "  class K; endclass\n"
      "endpackage\n"
      "class C; typedef byte key_t; endclass\n"
      "module top;\n"
      "  int a [p::idx_t];\n"
      "  int b [C::key_t];\n"
      "  int k [p::K];\n"
      "  int z [p::N];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  const auto& vars = design->top_modules[0]->variables;
  auto var = [&vars](std::string_view name) -> const RtlirVariable* {
    auto it = std::ranges::find(vars, name, &RtlirVariable::name);
    return it == vars.end() ? nullptr : &*it;
  };
  const RtlirVariable* a = var("a");
  const RtlirVariable* b = var("b");
  const RtlirVariable* k = var("k");
  const RtlirVariable* z = var("z");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  ASSERT_NE(k, nullptr);
  ASSERT_NE(z, nullptr);
  EXPECT_TRUE(a->is_assoc);
  EXPECT_EQ(a->assoc_index_width, 4u);
  EXPECT_FALSE(a->is_index_signed);
  EXPECT_TRUE(b->is_assoc);
  EXPECT_EQ(b->assoc_index_width, 8u);
  EXPECT_TRUE(b->is_index_signed);
  EXPECT_TRUE(k->is_assoc);
  EXPECT_TRUE(k->is_class_index);
  EXPECT_FALSE(z->is_assoc);
  EXPECT_EQ(z->unpacked_size, 4u);
}

TEST(UserDefinedTypeAssocArrayElaboration, ScopedRealIndexIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "package q; typedef real real_t; endpackage\n"
      "module top;\n"
      "  int r [q::real_t];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal type shall not be used as an "
                            "associative array index type",
                            3, "7.8.5"));
}

TEST(UserDefinedTypeAssocArrayElaboration, NetOfScopedIndexDimIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "package p; typedef bit [3:0] idx_t; class K; endclass endpackage\n"
      "module top;\n"
      "  wire w1 [p::idx_t];\n"
      "  wire w2 [p::K];\n"
      "  wire w3 [0:1];\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 4u, 5u}) {
    EXPECT_EQ(
        static_cast<bool>(ReportedError(
            f.diag.Diagnostics(),
            "a net's unpacked dimension must be fixed-size", line, "6.7")),
        line != 5u)
        << "line " << line;
  }
}

void ExpectKeywordIndexAssociative(const std::string& keyword) {
  ElabFixture f;
  auto* design = ElaborateSrc(std::format("module top;\n"
                                          "  int a [{0}];\n"
                                          "  wire w [{0}];\n"
                                          "endmodule\n",
                                          keyword),
                              f);
  ASSERT_NE(design, nullptr);
  const auto& vars = design->top_modules[0]->variables;
  auto a = std::ranges::find(vars, std::string_view("a"), &RtlirVariable::name);
  ASSERT_NE(a, vars.end());
  EXPECT_TRUE(a->is_assoc);
  EXPECT_EQ(a->assoc_index_width, 64u);
  EXPECT_FALSE(a->is_index_signed);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a net's unpacked dimension must be fixed-size", 3,
                            "6.7"));
}

TEST(UserDefinedTypeAssocArrayElaboration, ChandleIndexIsAssociative) {
  ExpectKeywordIndexAssociative("chandle");
}

TEST(UserDefinedTypeAssocArrayElaboration, EventIndexIsAssociative) {
  ExpectKeywordIndexAssociative("event");
}

TEST(UserDefinedTypeAssocArrayElaboration, DataTypeIndexFormsAreAssociative) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class P #(int N = 1); endclass\n"
      "module top;\n"
      "  bit [3:0] k;\n"
      "  real r;\n"
      "  int e [enum {A, B}];\n"
      "  int s [struct packed {bit [3:0] f;}];\n"
      "  int t [type(k)];\n"
      "  int c [P#(8)];\n"
      "  int z [type(r)];\n"
      "  int q [struct {real f;}];\n"
      "  int str [type(string)];\n"
      "  wire w [type(k)];\n"
      "  initial begin\n"
      "    int y [type(k)];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const auto& vars = design->top_modules[0]->variables;
  auto var = [&vars](std::string_view name) -> const RtlirVariable* {
    auto it = std::ranges::find(vars, name, &RtlirVariable::name);
    return it == vars.end() ? nullptr : &*it;
  };
  for (std::string_view name : {"e", "s", "t", "c", "str"}) {
    ASSERT_NE(var(name), nullptr) << name;
    EXPECT_TRUE(var(name)->is_assoc) << name;
  }
  EXPECT_EQ(var("e")->assoc_index_width, 32u);
  EXPECT_EQ(var("s")->assoc_index_width, 4u);
  EXPECT_EQ(var("t")->assoc_index_width, 4u);
  EXPECT_FALSE(var("t")->is_index_signed);
  EXPECT_TRUE(var("c")->is_class_index);
  EXPECT_TRUE(var("str")->is_string_index);
  const char* const kRealIndex =
      "real or shortreal type shall not be used as an associative array index "
      "type";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kRealIndex, 9, "7.8.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kRealIndex, 10, "7.8.5"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kRealIndex, 14, "7.8.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a net's unpacked dimension must be fixed-size", 12,
                            "6.7"));
}

TEST(AssocIndexTypeValidation, TypeRefRealIndexReportedInEveryScope) {
  ElabFixture f;
  ElaborateSrc(
      "package q; real r; bit [3:0] k;\n"
      "  int a [type(r)]; int b [type(k)];\n"
      "endpackage\n"
      "module top;\n"
      "  real r; bit [3:0] k;\n"
      "  class C; real cr; int p [type(cr)]; int n [type(k)]; endclass\n"
      "  function void g(int fa [type(r)]);\n"
      "    int fb [type(r)];\n"
      "    int fc [type(k)];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    int ya [type(r)];\n"
      "    int yb [type(k)];\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const std::string_view kMessage =
      "real or shortreal type shall not be used as an associative array index "
      "type";
  for (uint32_t line : {2u, 6u, 7u, 8u, 12u}) {
    EXPECT_TRUE(ReportedError(diags, kMessage, line, "7.8.5")) << line;
  }
  for (uint32_t line : {9u, 13u}) {
    EXPECT_FALSE(ReportedError(diags, kMessage, line, "7.8.5")) << line;
  }
}

TEST(AssocIndexTypeValidation, TypeRefIndexWithoutRealInTypedefIsNotReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  bit [3:0] k;\n"
      "  typedef int tk [type(k)];\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "real or shortreal type shall not be used as an "
                             "associative array index type",
                             3, "7.8.5"));
}

TEST(AssocIndexTypeValidation, TypedefTypeRefIndexIsResolvedInEveryScope) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "real ur; typedef int ut [type(ur)];\n"
      "package q; real r; typedef int qt [type(r)]; endpackage\n"
      "module top;\n"
      "  real r; bit [3:0] k;\n"
      "  typedef int mt [type(r)];\n"
      "  class C; real cr; typedef int ct [type(cr)]; endclass\n"
      "  typedef int tk [type(k)];\n"
      "  tk x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const auto& diags = f.diag.Diagnostics();
  const std::string_view kMessage =
      "real or shortreal type shall not be used as an associative array index "
      "type";
  for (uint32_t line : {1u, 2u, 5u, 6u}) {
    EXPECT_TRUE(ReportedError(diags, kMessage, line, "7.8.5")) << line;
  }
  const auto& vars = design->top_modules[0]->variables;
  auto x = std::ranges::find(vars, "x", &RtlirVariable::name);
  ASSERT_NE(x, vars.end());
  EXPECT_TRUE(x->is_assoc);
  EXPECT_EQ(x->assoc_index_width, 4u);
  EXPECT_FALSE(x->is_index_signed);
}

TEST(AssocIndexTypeValidation, TypeRefIndexOnVariablePortIsResolved) {
  ElabFixture f;
  ElaborateSrc(
      "module top (input var real r, input var int p [type(r)],\n"
      "            input var bit [3:0] k, input var int q [type(k)]);\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const std::string_view kMessage =
      "real or shortreal type shall not be used as an associative array index "
      "type";
  EXPECT_TRUE(ReportedError(diags, kMessage, 1, "7.8.5"));
  EXPECT_FALSE(ReportedError(diags, kMessage, 2, "7.8.5"));
}

TEST(UserDefinedIndexAssocArrayElaboration,
     RealtimeAndAggregatesHoldingARealAreReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef realtime rt_t;\n"
      "  typedef struct {shortreal r;} ss_t; typedef struct {realtime r;} "
      "st_t;\n"
      "  typedef union {real r; int i;} uu_t; typedef union tagged {real r; "
      "int i;} ut_t;\n"
      "  typedef struct {real r [2];} sa_t; typedef struct {real r [];} sd_t; "
      "typedef struct {real r [$];} sq_t;\n"
      "  typedef real ra_t [2]; typedef real rd_t []; typedef real rq_t [$]; "
      "typedef real rx_t [int];\n"
      "  int a1 [realtime];\n"
      "  int a2 [rt_t];\n"
      "  int a3 [ss_t];\n"
      "  int a4 [st_t];\n"
      "  int a5 [uu_t];\n"
      "  int a6 [ut_t];\n"
      "  int a7 [sa_t];\n"
      "  int a8 [sd_t];\n"
      "  int a9 [sq_t];\n"
      "  int b1 [ra_t];\n"
      "  int b2 [rd_t];\n"
      "  int b3 [rq_t];\n"
      "  int b4 [rx_t];\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line = 7; line <= 19; ++line) {
    EXPECT_TRUE(ReportedError(diags,
                              "real or shortreal type shall not be used as an "
                              "associative array index type",
                              line, "7.8.5"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 13u);
}

TEST(UserDefinedIndexAssocArrayElaboration,
     ClassWithARealPropertyAndArraysOfIntAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class C; real r; endclass\n"
      "module t;\n"
      "  typedef int id_t []; typedef int iq_t [$]; typedef int if_t [2]; "
      "typedef int ix_t [int];\n"
      "  typedef union {int a; byte b;} un_t;\n"
      "  int a [C]; int b [id_t]; int c [iq_t]; int d [if_t]; int e [ix_t]; "
      "int g [un_t];\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
