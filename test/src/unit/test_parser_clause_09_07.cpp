#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

TEST_F(FineGrainProcessControlParseTest, ProcessMethodCalls) {
  auto* unit = Parse(
      "module m;\n"
      "  initial begin\n"
      "    p.status();\n"
      "    p.kill();\n"
      "    p.await();\n"
      "    p.suspend();\n"
      "    p.resume();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
  auto& items = unit->modules[0]->items;
  ASSERT_GE(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kInitialBlock);
}

TEST_F(FineGrainProcessControlParseTest, ProcessScopeResolution) {
  auto* unit = Parse(
      "module m;\n"
      "  process::state_e st;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
  auto& items = unit->modules[0]->items;
  ASSERT_GE(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[0]->data_type.scope_name, "process");
  EXPECT_EQ(items[0]->data_type.type_name, "state_e");
}

TEST(FineGrainProcessControlParsing, ProcessSelfAssignment) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    process p;\n"
              "    p = process::self();\n"
              "  end\n"
              "endmodule\n"));
}

TEST(FineGrainProcessControlParsing, ProcessKillCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    process p;\n"
              "    p = process::self();\n"
              "    fork\n"
              "      begin\n"
              "        #100;\n"
              "      end\n"
              "    join_none\n"
              "    p.kill();\n"
              "  end\n"
              "endmodule\n"));
}

TEST(FineGrainProcessControlParsing, ProcessDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(FineGrainProcessControlParsing, ProcessStatusCheck) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    process p;\n"
              "    p = process::self();\n"
              "    if (p.status() != process::FINISHED)\n"
              "      $display(\"still running\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(FineGrainProcessControlParsing, ProcessPassedToTask) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task automatic do_work(process p);\n"
              "    p.kill();\n"
              "  endtask\n"
              "  initial begin\n"
              "    process p = process::self();\n"
              "    do_work(p);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(FineGrainProcessControlParsing, AllStateEnumMembers) {
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

TEST(FineGrainProcessControlParsing, ProcessComparedToNull) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    process p;\n"
              "    if (p != null)\n"
              "      p.kill();\n"
              "  end\n"
              "endmodule\n"));
}

TEST(FineGrainProcessControlParsing, ProcessArrayDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    process job[3];\n"
              "    job[0] = process::self();\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
