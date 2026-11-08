#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(ProcessStdPackageParser, BareDeclarationOfBuiltInType) {
  auto r = Parse(
      "module m;\n"
      "  process p;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

TEST(ProcessStdPackageParser, StaticSelfYieldsHandle) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    process p;\n"
              "    p = process::self();\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ProcessStdPackageParser, PrototypeMethodsParse) {
  auto r = Parse(
      "module m;\n"
      "  string st;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "    p.status();\n"
      "    p.kill();\n"
      "    p.await();\n"
      "    p.suspend();\n"
      "    p.resume();\n"
      "    p.srandom(7);\n"
      "    st = p.get_randstate();\n"
      "    p.set_randstate(st);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

TEST(ProcessStdPackageParser, StateEnumMembersParse) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    process p = process::self();\n"
              "    if (p.status() == process::FINISHED) ;\n"
              "    if (p.status() == process::RUNNING) ;\n"
              "    if (p.status() == process::WAITING) ;\n"
              "    if (p.status() == process::SUSPENDED) ;\n"
              "    if (p.status() == process::KILLED) ;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ProcessStdPackageParser, ScopedStateTypeNameParses) {
  auto r = Parse(
      "module m;\n"
      "  process::state st;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[0]->data_type.scope_name, "process");
  EXPECT_EQ(items[0]->data_type.type_name, "state");
}

TEST(ProcessStdPackageParser, ProcessAsSubroutineFormalType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task automatic do_work(process p);\n"
              "    p.kill();\n"
              "  endtask\n"
              "endmodule\n"));
}

TEST(ProcessStdPackageParser, ProcessArrayDeclaration) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    process job[3];\n"
              "    job[0] = process::self();\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
