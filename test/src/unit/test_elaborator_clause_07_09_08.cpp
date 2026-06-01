#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §7.9.8 — an integral argument matches an integral index type and is therefore
// assignment compatible; elaboration accepts it.
TEST(AssocTraversalArgElaboration, IntegralArgOnIntegralIndexOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int aa[int];\n"
             "  int k;\n"
             "  initial k = aa.first(k);\n"
             "endmodule\n"));
}

// §7.9.8 — a narrower integral argument is still assignment compatible with an
// integral index. The truncation it produces is a run-time effect, so
// elaboration must not reject it (the LRM's own example pairs an int index with
// a byte argument).
TEST(AssocTraversalArgElaboration, NarrowIntegralArgOnIntegralIndexOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int aa[int];\n"
             "  byte ix;\n"
             "  int status;\n"
             "  initial status = aa.first(ix);\n"
             "endmodule\n"));
}

// §7.9.8 — a string argument matches a string index type and is assignment
// compatible; elaboration accepts it.
TEST(AssocTraversalArgElaboration, StringArgOnStringIndexOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int aa[string];\n"
             "  string s;\n"
             "  initial s = aa.last(s);\n"
             "endmodule\n"));
}

// §7.9.8 — a string argument is not assignment compatible with an integral
// index type; elaboration must reject the traversal call.
TEST(AssocTraversalArgElaboration, StringArgOnIntegralIndexRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  string s;\n"
      "  initial s = aa.first(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.9.8 — an integral argument is not assignment compatible with a string
// index type; elaboration must reject the traversal call.
TEST(AssocTraversalArgElaboration, IntegralArgOnStringIndexRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int k;\n"
      "  initial k = aa.last(k);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.9.8 — the assignment-compatibility rule applies to every traversal method,
// not just first()/last(); next() with a mismatched argument is also rejected.
TEST(AssocTraversalArgElaboration, NextStringArgOnIntegralIndexRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  string s;\n"
      "  initial s = aa.next(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §7.9.8 — likewise prev() with a mismatched argument is rejected.
TEST(AssocTraversalArgElaboration, PrevIntegralArgOnStringIndexRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int k;\n"
      "  initial k = aa.prev(k);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
