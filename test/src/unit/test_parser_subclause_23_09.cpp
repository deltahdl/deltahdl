#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §23.9 lists a module among the constructs that define a new scope, so a type
// name declared inside one module is not a type name in the next. These cases
// fail when the parser carries such a name past `endmodule`: the later module
// reads the identifier as a data type and reports `expected identifier, got
// '='` where its parameter name stands. §3.12.1 draws the other edge of the
// same boundary, keeping a compilation-unit declaration visible throughout the
// unit, so the last case fails when a fix scopes every type name to the
// enclosing module.

// §6.20.3 declares a type parameter in the module's parameter_port_list and
// gives it no visibility outside. A.10.3 lets `data_type_or_implicit` be empty,
// so `parameter TP = 1` in the module after it is a value parameter named TP.
TEST(ModuleScopeParse, TypeParameterNameIsNotATypeInALaterModule) {
  auto r = Parse(
      "module a #(parameter type TP = logic) (); endmodule\n"
      "module b #(parameter TP = 1) (); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  auto* mod_b = r.cu->modules[1];
  EXPECT_EQ(mod_b->name, "b");
  ASSERT_EQ(mod_b->params.size(), 1u);
  EXPECT_EQ(mod_b->params[0].first, "TP");
  // A value parameter, not a type parameter: the identifier is the name the
  // declaration introduces rather than the type it was given.
  EXPECT_TRUE(mod_b->type_param_names.empty());
}

// The same rule reaches a `typedef` written in a module body, which §23.9
// scopes to that module exactly as it scopes a type parameter.
TEST(ModuleScopeParse, ModuleTypedefNameIsNotATypeInALaterModule) {
  auto r = Parse(
      "module a; typedef int T; endmodule\n"
      "module b #(parameter T = 1) (); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  auto* mod_b = r.cu->modules[1];
  EXPECT_EQ(mod_b->name, "b");
  ASSERT_EQ(mod_b->params.size(), 1u);
  EXPECT_EQ(mod_b->params[0].first, "T");
  EXPECT_TRUE(mod_b->type_param_names.empty());
}

// §6.20.3 makes a type parameter a type name inside the module that declares
// it, so `TP x;` in that body is a variable declaration of the named type TP.
// This case fails if the parser stops registering the type parameter at all.
TEST(ModuleScopeParse, TypeParameterIsStillATypeInsideItsOwnModule) {
  auto r = Parse(
      "module a #(parameter type TP = logic) ();\n"
      "  TP x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* item = FindItemByName(r.cu->modules[0]->items, "x");
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(item->data_type.type_name, "TP");
}

// §3.12.1 makes a declaration at compilation-unit scope visible throughout the
// compilation unit, so a typedef written there is a type name in every module
// of the unit and in the ones after the first as much as in the first.
TEST(ModuleScopeParse, CompilationUnitTypedefIsATypeInEveryModule) {
  auto r = Parse(
      "typedef int T;\n"
      "module a;\n"
      "  T x;\n"
      "endmodule\n"
      "module b;\n"
      "  T x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  for (auto* mod : r.cu->modules) {
    auto* item = FindItemByName(mod->items, "x");
    ASSERT_NE(item, nullptr) << "no declaration of x in module " << mod->name;
    EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
    EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed);
    EXPECT_EQ(item->data_type.type_name, "T");
  }
}

// §23.9's list of scopes runs past the design elements above: "Tasks,
// Functions, begin-end blocks (named or unnamed), fork-join blocks (named or
// unnamed), Generate blocks". A type name declared in one of those five is not
// a type name in the module after it, and the five cases below each declare one
// and then reuse the identifier outside the scope that declared it.
//
// Every case writes `localparam T = 1;` for the reuse, because A.2.1.1 gives a
// parameter declaration an optional data type: with T no longer a type name the
// declaration names T and leaves its type implicit, and with T still one the
// parser reads T as the type and reports `expected identifier` at the `=`. So
// the assertion is that the parse succeeded and produced a parameter named T,
// which is the arrangement the four cases above already use across a module
// boundary. Here the boundary is inside one module, since §23.9 scopes a module
// too and a leak across `endmodule` would be caught by those cases instead.
TEST(ModuleScopeParse, TaskTypedefNameIsNotATypeAfterItsTask) {
  auto r = Parse(
      "module m;\n"
      "  task t; typedef int T; endtask\n"
      "  localparam T = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* item = FindItemByName(r.cu->modules[0]->items, "T");
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kImplicit);
}

TEST(ModuleScopeParse, FunctionTypedefNameIsNotATypeAfterItsFunction) {
  auto r = Parse(
      "module m;\n"
      "  function int f; typedef int T; f = 0; endfunction\n"
      "  localparam T = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* item = FindItemByName(r.cu->modules[0]->items, "T");
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kImplicit);
}

// The unnamed form, which §23.9's parenthetical makes a scope as much as the
// named one.
TEST(ModuleScopeParse, BlockTypedefNameIsNotATypeAfterItsBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin typedef int T; end\n"
      "  localparam T = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* item = FindItemByName(r.cu->modules[0]->items, "T");
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kImplicit);
}

// A.6.3 gives a par_block its own block_item_declaration list, so the typedef
// stands directly between `fork` and `join`.
TEST(ModuleScopeParse, ForkTypedefNameIsNotATypeAfterItsFork) {
  auto r = Parse(
      "module m;\n"
      "  initial fork typedef int T; join\n"
      "  localparam T = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* item = FindItemByName(r.cu->modules[0]->items, "T");
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kImplicit);
}

// The generate block, not the generate region around it: §23.9 lists the block
// and §27.3 makes the region no scope at all, so the typedef goes inside the
// `begin` of the conditional generate construct and the reuse after
// `endgenerate`.
TEST(ModuleScopeParse, GenerateBlockTypedefNameIsNotATypeAfterIt) {
  auto r = Parse(
      "module m;\n"
      "  generate if (1) begin typedef int T; end endgenerate\n"
      "  localparam T = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* item = FindItemByName(r.cu->modules[0]->items, "T");
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kImplicit);
}

// The other edge of the same boundary. §23.9 scopes the name to the task rather
// than withdrawing it, so `T x;` in the task that declared T is a variable of
// the named type T. This case fails if the registration is dropped instead of
// scoped, which the five above would not notice.
TEST(ModuleScopeParse, TaskTypedefIsStillATypeInsideItsOwnTask) {
  auto r = Parse(
      "module m;\n"
      "  task t;\n"
      "    typedef int T;\n"
      "    T x;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* task = FindItemByName(r.cu->modules[0]->items, "t");
  ASSERT_NE(task, nullptr);
  const Stmt* decl = nullptr;
  for (const auto* s : task->func_body_stmts) {
    if (s->kind == StmtKind::kVarDecl && s->var_name == "x") decl = s;
  }
  ASSERT_NE(decl, nullptr);
  EXPECT_EQ(decl->var_decl_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(decl->var_decl_type.type_name, "T");
}

}  // namespace
