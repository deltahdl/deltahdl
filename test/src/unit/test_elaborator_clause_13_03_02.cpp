#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(TaskBodyElaboration, AutoTaskLocalInNonblockingAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    x <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(TaskBodyElaboration, AutoTaskModuleVarNonblockingOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  task automatic t();\n"
      "    x <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskBodyElaboration, StaticTaskLocalInNonblockingOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task static t();\n"
      "    int x;\n"
      "    x <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskBodyElaboration, DefaultTaskLocalInNonblockingOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    int x;\n"
      "    x <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskBodyElaboration, AutoTaskArgInNonblockingAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(output int y);\n"
      "    y <= 5;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(TaskBodyElaboration, AutoTaskLocalBlockingAssignOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    x = 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskBodyElaboration, AutoTaskStaticLocalInNonblockingOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    static int x;\n"
      "    x <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskBodyElaboration, StaticTaskAutoLocalInNonblockingError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task static t();\n"
      "    automatic int x;\n"
      "    x <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(TaskBodyElaboration, AutoTaskInoutArgInNonblockingError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(inout int v);\n"
      "    v <= 5;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(TaskBodyElaboration, AutoTaskLocalInNestedNonblockingError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    if (1) begin\n"
      "      x <= 1;\n"
      "    end\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(TaskBodyElaboration, DefaultTaskAutoLocalInNonblockingError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    automatic int x;\n"
      "    x <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
