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

}  // namespace
