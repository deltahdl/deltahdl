#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(UserDefinedTypeElaboration, TypedefNamedResolution) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef logic [15:0] word_t;\n"
      "  word_t data;\n"
      "  initial data = 1234;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "data") {
      EXPECT_EQ(v.width, 16u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(UserDefinedTypeElaboration, TypedefChain) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  typedef byte_t octet_t;\n"
      "  octet_t val;\n"
      "  initial val = 255;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "val") {
      EXPECT_EQ(v.width, 8u);
      EXPECT_TRUE(v.is_4state);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(UserDefinedTypeElaboration, TypedefChainSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef int my_int;\n"
      "  my_int x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  for (const auto& v : mod->variables) {
    if (v.name == "x") {
      EXPECT_EQ(v.width, 32u);
      EXPECT_TRUE(v.is_signed);
    }
  }
}

TEST(UserDefinedTypeElaboration, TypedefStructWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  for (const auto& v : mod->variables) {
    if (v.name == "p") {
      EXPECT_EQ(v.width, 16u);
    }
  }
}

TEST(UserDefinedTypeElaboration, TypedefUnionWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union packed { logic [7:0] a; logic [7:0] b; } val_t;\n"
      "  val_t u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "u") {
      EXPECT_EQ(v.width, 8u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(UserDefinedTypeElaboration, ForwardTypedefThenDefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum color_e;\n"
      "  typedef enum {RED, GREEN, BLUE} color_e;\n"
      "  color_e c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UserDefinedTypeElaboration, BareForwardTypedefThenDefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef my_type;\n"
      "  typedef int my_type;\n"
      "  my_type x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UserDefinedTypeElaboration, TypedefChain2State) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit [7:0] ubyte_t;\n"
      "  typedef ubyte_t alias_t;\n"
      "  alias_t val;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  for (const auto& v : mod->variables) {
    if (v.name == "val") {
      EXPECT_EQ(v.width, 8u);
      EXPECT_FALSE(v.is_4state);
    }
  }
}

TEST(UserDefinedTypeElaboration, MultipleForwardTypedefsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef class myclass;\n"
      "  typedef class myclass;\n"
      "  class myclass;\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UserDefinedTypeElaboration, ForwardEnumWithStructDefinition_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef enum my_t;\n"
      "  typedef struct packed { int A; int B; } my_t;\n"
      "  my_t x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typedef 'my_t' does not conform to its forward declaration as enum", 3,
      "6.18"));
}

TEST(UserDefinedTypeElaboration, ForwardStructWithEnumDefinition_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct my_t;\n"
      "  typedef enum {RED, GREEN, BLUE} my_t;\n"
      "  my_t x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typedef 'my_t' does not conform to its forward declaration as struct", 3,
      "6.18"));
}

TEST(UserDefinedTypeElaboration, ForwardUnionWithEnumDefinition_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef union my_t;\n"
      "  typedef enum {A, B} my_t;\n"
      "  my_t x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typedef 'my_t' does not conform to its forward declaration as union", 3,
      "6.18"));
}

TEST(UserDefinedTypeElaboration, ForwardClassTypedefWithDataDefinition_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef class C;\n"
      "  typedef int C;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typedef 'C' does not conform to its forward declaration as class", 3,
      "6.18"));
}

TEST(UserDefinedTypeElaboration,
     ForwardInterfaceClassTypedefWithDataDefinition_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef interface class IC;\n"
      "  typedef int IC;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typedef 'IC' does not conform to its forward declaration as class", 3,
      "6.18"));
}

TEST(UserDefinedTypeElaboration, MultipleForwardEnumDeclarations) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum color_e;\n"
      "  typedef enum color_e;\n"
      "  typedef enum {RED, GREEN, BLUE} color_e;\n"
      "  color_e c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UserDefinedTypeElaboration, ForwardTypedefAfterFinalDefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  typedef struct pair_t;\n"
      "  pair_t p;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "p") {
      EXPECT_EQ(v.width, 16u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(UserDefinedTypeElaboration, ForwardTypedefResolvedInGenerateBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  generate\n"
      "    for (genvar i = 0; i < 1; i = i + 1) begin : g\n"
      "      typedef enum color_e;\n"
      "      typedef enum {RED, GREEN, BLUE} color_e;\n"
      "      color_e c;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UserDefinedTypeElaboration, UnresolvedForwardTypedefInModule_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef enum color_e;\n"
      "  color_e c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "forward typedef 'color_e' is never resolved by a "
                            "definition in the same scope",
                            2, "6.18"));
}

TEST(UserDefinedTypeElaboration, UnresolvedBareForwardTypedefInModule_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef my_type;\n"
      "  my_type x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "forward typedef 'my_type' is never resolved by a "
                            "definition in the same scope",
                            2, "6.18"));
}

TEST(UserDefinedTypeElaboration,
     GenerateBlockForwardTypedefWithNoDefinitionInTheBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a; } pair_t;\n"
      "  if (1) begin : g\n"
      "    typedef struct pair_t;\n"
      "    pair_t p;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "forward typedef 'pair_t' is never resolved by a "
                            "definition in the same scope",
                            4, "6.18"));
}

TEST(UserDefinedTypeElaboration,
     GenerateBlockForwardTypedefDefinedInTheBlockIsNotReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  if (1) begin : g\n"
      "    typedef union pair_t;\n"
      "    pair_t p;\n"
      "    typedef union { int a; int b; } pair_t;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "forward typedef 'pair_t' is never resolved by a "
                             "definition in the same scope",
                             3, "6.18"));
}

TEST(UserDefinedTypeElaboration,
     NestedAndElseGenerateBlockForwardTypedefsAreJudgedInTheirOwnBlock) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  if (1) begin : g\n"
      "    typedef enum { A, B } col_t;\n"
      "    if (1) begin : h\n"
      "      typedef enum col_t;\n"
      "    end\n"
      "  end else begin : e\n"
      "    typedef struct row_t;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "forward typedef 'col_t' is never resolved by a "
                            "definition in the same scope",
                            5, "6.18"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "forward typedef 'row_t' is never resolved by a "
                            "definition in the same scope",
                            8, "6.18"));
}

TEST(UserDefinedTypeElaboration, ForwardTypedefScopePrefixNotClass_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef T_fwd;\n"
      "  typedef int T_fwd;\n"
      "  typedef T_fwd::Inner inner_t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "scope-resolution prefix 'T_fwd' of a typedef does not "
                    "resolve to a class",
                    4, "6.18"));
}

TEST(UserDefinedTypeElaboration, ForwardTypedefScopePrefixClass_Legal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef class C;\n"
      "  class C;\n"
      "    typedef int T;\n"
      "  endclass\n"
      "  typedef C::T t_alias;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UserDefinedTypeElaboration, QueueTypedefDeclaresAQueue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef string T_SQ[$];\n"
      "  T_SQ sq;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  const auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_queue);
}

TEST(UserDefinedTypeElaboration, DynamicArrayTypedefDeclaresADynamicArray) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef int T_DA[];\n"
      "  T_DA da;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  const auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_dynamic);
}

TEST(UserDefinedTypeElaboration, FixedArrayTypedefStillSizesTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef int T_FA[3];\n"
      "  T_FA fa;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  const auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_EQ(vars[0].unpacked_size, 3u);
  EXPECT_FALSE(vars[0].is_queue);
  EXPECT_FALSE(vars[0].is_dynamic);
}

TEST(UserDefinedTypeElaboration, TypeReferenceBeforeItsDeclarationIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  my_type x;\n"
      "  typedef int my_type;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of type 'my_type' does not precede "
                            "this reference to it",
                            2, "6.18"));
}

TEST(UserDefinedTypeElaboration,
     TypeReferenceBeforeItsDeclarationInAListIsReportedOnce) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  my_type a, b, c;\n"
      "  typedef int my_type;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of type 'my_type' does not precede "
                            "this reference to it",
                            2, "6.18"));
  int reports = 0;
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.message.find("does not precede") != std::string::npos) ++reports;
  }
  EXPECT_EQ(reports, 1);
}

TEST(UserDefinedTypeElaboration,
     NameThatIsNeitherTypeNorModuleIsReportedAsAnUndeclaredType) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  nosuch x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of type 'nosuch' does not precede "
                            "this reference to it",
                            2, "6.18"));
}

TEST(UserDefinedTypeElaboration,
     TypeDeclaredInAPackageNeverImportedIsStillAnUndeclaredTypeReference) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  typedef int my_type;\n"
      "endpackage\n"
      "module m;\n"
      "  my_type x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of type 'my_type' does not precede "
                            "this reference to it",
                            5, "6.18"));
}

TEST(UserDefinedTypeElaboration, AggregateTypedefIsRecordedWithNoWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef int i_t;\n"
      "  typedef int arr_t[4];\n"
      "  typedef int q_t[$];\n"
      "  typedef byte da_t[];\n"
      "  typedef int aa_t[string];\n"
      "  i_t v;\n"
      "  initial v = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto width_of = [design](std::string_view name) -> int64_t {
    auto it = design->type_widths.find(name);
    if (it == design->type_widths.end()) return -1;
    return it->second;
  };
  EXPECT_EQ(width_of("i_t"), 32);
  EXPECT_EQ(width_of("arr_t"), 0);
  EXPECT_EQ(width_of("q_t"), 0);
  EXPECT_EQ(width_of("da_t"), 0);
  EXPECT_EQ(width_of("aa_t"), 0);
}

TEST(UserDefinedTypeElaboration, CompilationUnitAggregateTypedefHasNoWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "typedef int cu_i_t;\n"
      "typedef int cu_arr_t[4];\n"
      "module t;\n"
      "  cu_i_t v;\n"
      "  initial v = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->type_widths["cu_i_t"], 32u);
  EXPECT_EQ(design->type_widths["cu_arr_t"], 0u);
}

TEST(UserDefinedTypeElaboration, ImportedAggregateTypedefHasNoWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef int p_i_t;\n"
      "  typedef int p_arr_t[4];\n"
      "endpackage\n"
      "module t;\n"
      "  import p::*;\n"
      "  p_i_t v;\n"
      "  initial v = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->type_widths["p_i_t"], 32u);
  EXPECT_EQ(design->type_widths["p_arr_t"], 0u);
}

TEST(UserDefinedTypeElaboration,
     ClassMethodFormalMemberNamingATypedefDefinedBelowIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  class C;\n"
      "    function int f(union tagged { void N; pair_t A; } a);\n"
      "      return a.A.a;\n"
      "    endfunction\n"
      "  endclass\n"
      "  typedef struct { int a, b; } pair_t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of type 'pair_t' does not precede "
                            "this reference to it",
                            3, "6.18"));
}

TEST(UserDefinedTypeElaboration,
     ClassMethodFormalMemberNamingAForwardDeclaredTypedefIsClean) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct pair_t;\n"
      "  class C;\n"
      "    function int f(union tagged { void N; pair_t A; } a);\n"
      "      return a.A.a;\n"
      "    endfunction\n"
      "  endclass\n"
      "  typedef struct { int a, b; } pair_t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UserDefinedTypeElaboration,
     FormalStructMemberNamingAnUndeclaredTypeIsReportedOnce) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  function int f(struct { nosuch_t m; int c; } a);\n"
      "    return a.c;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of type 'nosuch_t' does not precede "
                            "this reference to it",
                            2, "6.18"));
  int reports = 0;
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.message.find("does not precede") != std::string::npos) ++reports;
  }
  EXPECT_EQ(reports, 1);
}

TEST(UserDefinedTypeElaboration,
     FormalStructMemberNamingADeclaredTypedefIsClean) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a, b; } pair_t;\n"
      "  function int f(struct { pair_t m; int c; } a);\n"
      "    return a.m.a + a.c;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UserDefinedTypeElaboration,
     GenerateBlockTypedefIsNotJudgedByTheModuleForwardTypedef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef struct pair_t;\n"
      "  typedef struct { int a; } pair_t;\n"
      "  if (1) begin : g\n"
      "    typedef union { int a; int b; } pair_t;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UserDefinedTypeElaboration,
     GenerateBlockDefinitionNotConformingToTheBlockForwardTypedefIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  if (1) begin : g\n"
      "    typedef struct pair_t;\n"
      "    typedef union { int a; int b; } pair_t;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typedef 'pair_t' does not conform to its forward declaration as struct",
      4, "6.18"));
}

TEST(UserDefinedTypeElaboration,
     ModuleDefinitionBelowAGenerateBlockIsJudgedByTheModuleForwardTypedef) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct pair_t;\n"
      "  if (1) begin : g\n"
      "    typedef union { int a; int b; } pair_t;\n"
      "  end\n"
      "  typedef union { int a; int b; } pair_t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typedef 'pair_t' does not conform to its forward declaration as struct",
      6, "6.18"));
  int reports = 0;
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.message.find("does not conform") != std::string::npos) ++reports;
  }
  EXPECT_EQ(reports, 1);
}

TEST(UserDefinedTypeElaboration,
     SiblingGenerateBlockForwardTypedefDoesNotJudgeALaterBlockDefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  if (1) begin : g\n"
      "    typedef struct pair_t;\n"
      "    typedef struct { int a; } pair_t;\n"
      "  end\n"
      "  if (1) begin : h\n"
      "    typedef union { int a; int b; } pair_t;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UserDefinedTypeElaboration,
     NestedGenerateBlockForwardTypedefDoesNotJudgeTheEnclosingDefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  if (1) begin : g\n"
      "    if (1) begin : h\n"
      "      typedef enum pair_t;\n"
      "      typedef enum { A, B } pair_t;\n"
      "    end\n"
      "    typedef struct { int a; } pair_t;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UserDefinedTypeElaboration,
     EnclosingBlockForwardTypedefJudgesItsDefinitionBelowANestedBlock) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  if (1) begin : g\n"
      "    typedef struct pair_t;\n"
      "    if (1) begin : h\n"
      "      typedef struct { int a; } pair_t;\n"
      "    end\n"
      "    typedef union { int a; int b; } pair_t;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typedef 'pair_t' does not conform to its forward declaration as struct",
      7, "6.18"));
}

TEST(UserDefinedTypeElaboration, ResolvedTypeKindFollowsAChainOfNames) {
  DataType integer;
  integer.kind = DataTypeKind::kInteger;
  DataType to_integer;
  to_integer.kind = DataTypeKind::kNamed;
  to_integer.type_name = "int_t";
  const TypedefMap kChain{{"int_t", integer}, {"alias_t", to_integer}};
  DataType written;
  written.kind = DataTypeKind::kNamed;
  written.type_name = "alias_t";
  EXPECT_EQ(ResolvedTypeKind(written, kChain), DataTypeKind::kInteger);

  DataType to_b;
  to_b.kind = DataTypeKind::kNamed;
  to_b.type_name = "b_t";
  DataType to_a;
  to_a.kind = DataTypeKind::kNamed;
  to_a.type_name = "a_t";
  const TypedefMap kCycle{{"a_t", to_b}, {"b_t", to_a}};
  EXPECT_EQ(ResolvedTypeKind(to_a, kCycle), DataTypeKind::kNamed);
}

}  // namespace
