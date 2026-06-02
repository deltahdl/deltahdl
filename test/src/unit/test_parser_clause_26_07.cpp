#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(StdBuiltinPackageParsing, ModuleWildcardImportOfStd) {
  auto r = Parse(
      "module m;\n"
      "  import std::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  const auto* imp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kImportDecl);
  ASSERT_NE(imp, nullptr);
  EXPECT_EQ(imp->import_item.package_name, "std");
  EXPECT_TRUE(imp->import_item.is_wildcard);
}

TEST(StdBuiltinPackageParsing, StdScopeResolutionCallWithArgument) {

  // built_in_function_call ::= [ std :: ] function_subroutine_call. Observe
  // that the optional `std ::` prefix is captured: the callee resolves through
  // a member-access whose base is the `std` package name.
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    std::randomize(x);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* call = FirstInitialExpr(r);
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(call->kind, ExprKind::kCall);
  ASSERT_NE(call->lhs, nullptr);
  EXPECT_EQ(call->lhs->kind, ExprKind::kMemberAccess);
  ASSERT_NE(call->lhs->lhs, nullptr);
  EXPECT_EQ(call->lhs->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(call->lhs->lhs->text, "std");
  ASSERT_NE(call->lhs->rhs, nullptr);
  EXPECT_EQ(call->lhs->rhs->text, "randomize");
  EXPECT_EQ(call->args.size(), 1u);
}

TEST(StdBuiltinPackageParsing, StdScopeResolutionCallNoArguments) {

  // built_in_function_call ::= [ std :: ] function_subroutine_call, where the
  // call carries an empty argument list (mirrors the LRM's `std::sys_task()`
  // example). The optional `std ::` prefix must still be captured as the base
  // of the callee, and the call must parse as a call with no arguments rather
  // than being mistaken for a scoped data reference.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    std::sys_task();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* call = FirstInitialExpr(r);
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(call->kind, ExprKind::kCall);
  ASSERT_NE(call->lhs, nullptr);
  EXPECT_EQ(call->lhs->kind, ExprKind::kMemberAccess);
  ASSERT_NE(call->lhs->lhs, nullptr);
  EXPECT_EQ(call->lhs->lhs->text, "std");
  ASSERT_NE(call->lhs->rhs, nullptr);
  EXPECT_EQ(call->lhs->rhs->text, "sys_task");
  EXPECT_EQ(call->args.size(), 0u);
}

TEST(StdBuiltinPackageParsing, StdScopedDataTypeInVariableDeclaration) {

  // built_in_data_type ::= [ std :: ] data_type_identifier. Observe that the
  // optional `std ::` prefix lands as the scope qualifier on the parsed type.
  auto r = Parse(
      "module m;\n"
      "  std::mailbox mb;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* var = FindItemByKind(r, ModuleItemKind::kVarDecl);
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->data_type.scope_name, "std");
  EXPECT_EQ(var->data_type.type_name, "mailbox");
  EXPECT_EQ(var->name, "mb");
}

TEST(StdBuiltinPackageParsing, StdScopedDataTypeIsNotNameSpecific) {

  // built_in_data_type accepts any data_type_identifier after `std ::`, not a
  // hard-coded set of names. A different built-in type identifier must produce
  // the same scoped variable declaration rather than a module instantiation.
  auto r = Parse(
      "module m;\n"
      "  std::semaphore sem;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* var = FindItemByKind(r, ModuleItemKind::kVarDecl);
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->data_type.scope_name, "std");
  EXPECT_EQ(var->data_type.type_name, "semaphore");
  EXPECT_EQ(var->name, "sem");
}

TEST(StdBuiltinPackageParsing, UserPackageNamedStdParses) {

  auto r = Parse(
      "package std;\n"
      "  typedef int t;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "std");
}

}
