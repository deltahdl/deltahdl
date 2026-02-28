// §8.20: Virtual methods

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA26, FuncDynamicOverrideInitial) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :initial int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA26, FuncDynamicOverrideExtends) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :extends int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA26, FuncDynamicOverrideFinal) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :final int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA26, FuncDynamicOverrideInitialFinal) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :initial :final int foo();\n"
      "    return 0;\n  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA26, FuncDynamicOverrideExtendsFinal) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :extends :final int foo();\n"
      "    return 0;\n  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA27, TaskDynamicOverrideInitial) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :initial my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA27, TaskDynamicOverrideExtends) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :extends my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA27, TaskDynamicOverrideFinal) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :final my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA27, TaskDynamicOverrideInitialFinal) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :initial :final my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA27, TaskDynamicOverrideExtendsFinal) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :extends :final my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
