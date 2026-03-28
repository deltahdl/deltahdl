#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(QueueAssignElaboration, QueueConcatElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(QueueAssignElaboration, EmptyConcatElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(QueueAssignElaboration, SelfConcatAppendElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {q, 6};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(QueueAssignElaboration, SelfConcatPrependElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {5, q};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(QueueAssignElaboration, SlicePopFrontElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = q[1:$];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(QueueAssignElaboration, SlicePopBackElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = q[0:$-1];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(QueueAssignElaboration, ConcatInsertAtPosElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  int pos;\n"
      "  initial q = {q[0:pos-1], 99, q[pos:$]};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

}  // namespace
