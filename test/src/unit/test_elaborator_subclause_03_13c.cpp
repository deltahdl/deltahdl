// Tests for §3.13 (e)'s module name space as it reaches a typedef's unpacked
// dimensions. A typedef an interface declares is a name of the interface
// alone, so a module elaborated after it that declares a typedef of the same
// name with no unpacked dimensions takes none of the interface's, for any
// declaration written with that name.

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
  const RtlirVariable* gv = nullptr;
  for (const RtlirVariable& var : m->variables) {
    if (var.name.ends_with("gv")) gv = &var;
  }
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

}  // namespace
