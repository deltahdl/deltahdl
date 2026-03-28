
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ClassOverviewParsing, ClassContainsBothPropertiesAndMethods) {
  auto r = Parse(
      "class Packet;\n"
      "  bit [3:0] command;\n"
      "  integer status;\n"
      "  task clean();\n"
      "    command = 0;\n"
      "  endtask\n"
      "  function integer current_status();\n"
      "    current_status = status;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];

  int prop_count = 0;
  int method_count = 0;
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty) ++prop_count;
    if (m->kind == ClassMemberKind::kMethod) ++method_count;
  }
  EXPECT_GE(prop_count, 2);
  EXPECT_GE(method_count, 2);
}

TEST(ClassOverviewParsing, MethodsIncludeBothFunctionsAndTasks) {
  auto r = Parse(
      "class C;\n"
      "  int x;\n"
      "  function int get_x();\n"
      "    get_x = x;\n"
      "  endfunction\n"
      "  task set_x(int val);\n"
      "    x = val;\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];

  bool has_function = false;
  bool has_task = false;
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method) {
      if (m->method->kind == ModuleItemKind::kFunctionDecl) has_function = true;
      if (m->method->kind == ModuleItemKind::kTaskDecl) has_task = true;
    }
  }
  EXPECT_TRUE(has_function);
  EXPECT_TRUE(has_task);
}

}  // namespace
