#include <gtest/gtest.h>

#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_rtlir_lookup.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace {

const char* const kSrc =
    "interface ifc;\n"
    "  typedef int t [2];\n"
    "endinterface\n"
    "module m (ifc p);\n"
    "  typedef struct { int a; int b; } t;\n"
    "  t v;\n"
    "  if (1) begin : g\n"
    "    t gv;\n"
    "  end\n"
    "  function automatic t f(t a);\n"
    "    t q;\n"
    "    q = a;\n"
    "    return q;\n"
    "  endfunction\n"
    "endmodule\n"
    "module top;\n"
    "  ifc i ();\n"
    "  m u (i);\n"
    "endmodule\n";

const RtlirVariable* FindVarEndingWith(const RtlirModule* m,
                                       std::string_view suffix) {
  for (const RtlirVariable& var : m->variables) {
    if (var.name.ends_with(suffix)) return &var;
  }
  return nullptr;
}

TEST(ModuleNameSpaceTypedefDims, VariableTakesNoneOfAnInterfacesDimensions) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(kSrc, f, "top");
  ASSERT_NE(design, nullptr);
  const RtlirVariable* v = FindVar(design, "m", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->unpacked_size, 0u);
}

TEST(ModuleNameSpaceTypedefDims, GenerateBlockVariableTakesNoneOfThem) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(kSrc, f, "top");
  ASSERT_NE(design, nullptr);
  const RtlirModule* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  const RtlirVariable* gv = FindVarEndingWith(m, "gv");
  ASSERT_NE(gv, nullptr);
  EXPECT_EQ(gv->unpacked_size, 0u);
}

TEST(ModuleNameSpaceTypedefDims, SubroutineDeclarationsTakeNoneOfThem) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(kSrc, f, "top");
  ASSERT_NE(design, nullptr);
  const RtlirModule* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  ASSERT_EQ(m->function_decls.size(), 1u);
  const ModuleItem* fn = m->function_decls[0];
  ASSERT_FALSE(fn->func_body_stmts.empty());
  EXPECT_TRUE(fn->func_args[0].unpacked_dims.empty());
  EXPECT_TRUE(fn->return_array_dims.empty());
  EXPECT_TRUE(fn->func_body_stmts[0]->var_unpacked_dims.empty());
}

const char* const kBlockSrc =
    "module m;\n"
    "  typedef int t [2];\n"
    "  if (1) begin : g\n"
    "    if (1) begin : h\n"
    "      typedef struct { int a; int b; } t;\n"
    "      t hv;\n"
    "    end\n"
    "    if (1) begin : k\n"
    "      class t;\n"
    "        int v;\n"
    "      endclass\n"
    "      t kv;\n"
    "    end\n"
    "    t gv;\n"
    "  end\n"
    "  t mv;\n"
    "endmodule\n";

TEST(BlockNameSpaceTypedefDims, BlockTypedefHidesTheModulesDimensions) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(kBlockSrc, f, "m");
  ASSERT_NE(design, nullptr);
  const RtlirModule* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  const RtlirVariable* hv = FindVarEndingWith(m, "hv");
  ASSERT_NE(hv, nullptr);
  EXPECT_EQ(hv->unpacked_size, 0u);
}

TEST(BlockNameSpaceTypedefDims, BlockClassHidesTheModulesArrayTypedef) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(kBlockSrc, f, "m");
  ASSERT_NE(design, nullptr);
  const RtlirModule* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  const RtlirVariable* kv = FindVarEndingWith(m, "kv");
  ASSERT_NE(kv, nullptr);
  EXPECT_EQ(kv->unpacked_size, 0u);
}

TEST(BlockNameSpaceTypedefDims, EnclosingScopesKeepTheirDimensionsAfterIt) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(kBlockSrc, f, "m");
  ASSERT_NE(design, nullptr);
  const RtlirModule* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  const RtlirVariable* gv = FindVarEndingWith(m, "gv");
  ASSERT_NE(gv, nullptr);
  EXPECT_EQ(gv->unpacked_size, 2u);
  const RtlirVariable* mv = FindVar(design, "m", "mv");
  ASSERT_NE(mv, nullptr);
  EXPECT_EQ(mv->unpacked_size, 2u);
}

}  // namespace
