// Tests for §3.13 (e)'s module name space as it reaches a typedef's unpacked
// dimensions. A typedef an interface declares is a name of the interface
// alone, so a module elaborated after it that declares a typedef of the same
// name with no unpacked dimensions takes none of the interface's, for any
// declaration written with that name. §3.13 (f)'s block name space does the
// same for a generate block's typedef or class within the module.

#include <gtest/gtest.h>

#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_rtlir_lookup.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace {

// The interface's array typedef `t` is elaborated before the module `m`
// connected to it, which declares a structure typedef `t` of its own and,
// after it, a variable, a generate block's variable and a function's formal,
// return type and procedural variable, each written with that name.
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

// The variable of `m` whose hierarchical name ends with `suffix`, the name a
// generate block's variable is recorded by.
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

// A conditional generate's body is elaborated after every module has been, in
// the scope of the module it was written in.
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

// The module's array typedef `t`, hidden within the nested block `h` by a
// structure typedef and within the nested block `k` by a class, each written
// with no unpacked dimensions, and in force again for `g`'s variable after
// both blocks and for the module's own variable.
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

// §3.13 (f) with §27.5: a generate block's typedef stands over the module's
// for the block's items. The block's typedef left the module's two dimensions
// in the dimension table, and the block's variable took them.
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

// §3.13 (f) with §3.12.1: a generate block's class hides the module's typedef
// of its name, so the block's variable written with it is a handle.
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

// The hiding ends with the block: the enclosing block's variable written after
// the nested blocks, and the module's, keep the module's two elements.
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
