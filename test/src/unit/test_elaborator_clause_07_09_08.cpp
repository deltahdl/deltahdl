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
// index type; elaboration must reject the traversal call. The int result is
// captured in an int variable so the only type conflict elaboration can see is
// the string argument against the int index type -- isolating this rule from
// any return-value assignment check.
TEST(AssocTraversalArgElaboration, StringArgOnIntegralIndexRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  string s;\n"
      "  int status;\n"
      "  initial status = aa.first(s);\n"
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
// The int result is captured in an int variable so the sole type conflict is
// the string argument against the int index type.
TEST(AssocTraversalArgElaboration, NextStringArgOnIntegralIndexRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  string s;\n"
      "  int status;\n"
      "  initial status = aa.next(s);\n"
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

// §7.9.8 — the rule applies wherever a traversal call appears, not only on the
// right-hand side of an assignment. Here the call sits in an if condition (the
// same position the clause's own do/while traversal examples use); its integral
// result is a valid boolean, so the only conflict elaboration can flag is the
// string argument against the int index type.
TEST(AssocTraversalArgElaboration,
     ConditionPositionStringArgOnIntegralIndexRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  string s;\n"
      "  int status;\n"
      "  initial if (aa.first(s)) status = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
