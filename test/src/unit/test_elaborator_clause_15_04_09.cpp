#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(MailboxParameterizedElaborator, ParameterizedIntDeclaration) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].class_type_name, "mailbox");
}

TEST(MailboxParameterizedElaborator, ParameterizedWithMethodCalls) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  int msg;\n"
      "  initial begin\n"
      "    mb.put(42);\n"
      "    mb.get(msg);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.4.9: for a parameterized mailbox the compiler verifies that a put()
// argument is type-equivalent to the mailbox element type. Passing a string
// variable to a `mailbox #(int)` is a mismatch the compiler must reject up
// front rather than leaving it to a run-time error. The offending variable is
// declared with real §15.4.3 send syntax so the check runs on the produced
// input, not a hand-built state.
TEST(MailboxParameterizedElaborator, MismatchedPutVariableRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  string s;\n"
      "  initial begin\n"
      "    mb.put(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §15.4.9: the same compile-time check catches a mistyped literal — a string
// literal sent to a `mailbox #(int)`.
TEST(MailboxParameterizedElaborator, MismatchedPutLiteralRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  initial begin\n"
      "    mb.put(\"hello\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §15.4.9: the receive methods are checked too — a get() destination must be
// type-equivalent to the mailbox element type, so retrieving into an int from a
// `mailbox #(string)` is rejected. Built from real §15.4.5 get() syntax.
TEST(MailboxParameterizedElaborator, MismatchedGetDestinationRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(string) mb;\n"
      "  int n;\n"
      "  initial begin\n"
      "    mb.get(n);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §15.4.9: the standard's own example — a `typedef mailbox #(string)`, a
// matching put() of a string literal and a get() into a string variable. Every
// argument is type-equivalent, so the compiler accepts it. This exercises the
// check's typedef resolution of the parameterized element type, with the
// message built from real §15.4.3 put() and §15.4.5 get() syntax.
TEST(MailboxParameterizedElaborator, TypedefMatchingArgsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef mailbox #(string) s_mbox;\n"
      "  s_mbox sm;\n"
      "  string s;\n"
      "  initial begin\n"
      "    sm.put(\"hello\");\n"
      "    sm.get(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §15.4.9: the default (typeless / dynamic_type) mailbox imposes no
// compile-time type constraint — the same string-into-int-mailbox usage that a
// parameterized mailbox rejects is accepted here, because a dynamic mailbox
// defers type checking to run time. This isolates the check to the
// parameterized form.
TEST(MailboxParameterizedElaborator, DynamicMailboxNotTypeChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  string s;\n"
      "  initial begin\n"
      "    mb.put(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §15.4.9 enumerates six methods the compiler type-checks for a parameterized
// mailbox — put, try_put, peek, try_peek, get, and try_get. The put()/get()
// forms are exercised above; the following observe the same compile-time check
// firing on the remaining four, so the whole enumerated method set is covered.
// Each sends/receives a string against a `mailbox #(int)`, a mismatch the
// compiler must reject. The try_* methods return a status, assigned as in real
// §15.4.4/§15.4.6/§15.4.8 usage; peek() is a task called as a statement
// (§15.4.7).
TEST(MailboxParameterizedElaborator, MismatchedTryPutRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  string s;\n"
      "  int got;\n"
      "  initial begin\n"
      "    got = mb.try_put(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(MailboxParameterizedElaborator, MismatchedPeekRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  string s;\n"
      "  initial begin\n"
      "    mb.peek(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(MailboxParameterizedElaborator, MismatchedTryPeekRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  string s;\n"
      "  int got;\n"
      "  initial begin\n"
      "    got = mb.try_peek(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(MailboxParameterizedElaborator, MismatchedTryGetRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  string s;\n"
      "  int got;\n"
      "  initial begin\n"
      "    got = mb.try_get(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §15.4.9: the element type of a parameterized mailbox may be a real type, a
// distinct admitted type category from the integral and string cases above.
// Sending a string into a `mailbox #(real)` is a mismatch the compiler rejects,
// exercising the real-typed element form of the check.
TEST(MailboxParameterizedElaborator, RealElementRejectsStringArgument) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(real) mb;\n"
      "  string s;\n"
      "  initial begin\n"
      "    mb.put(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §15.4.9: a real-typed argument is likewise checked — a real literal sent to a
// `mailbox #(int)` is not type-equivalent to the integral element type and is
// rejected. This exercises the real-literal argument form of the check.
TEST(MailboxParameterizedElaborator, RealLiteralIntoIntMailboxRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  initial begin\n"
      "    mb.put(1.5);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §15.4.9: the accepting side of the real-typed element form — a real variable
// sent to a `mailbox #(real)` is type-equivalent, so the compiler accepts it.
TEST(MailboxParameterizedElaborator, RealElementAcceptsRealArgument) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(real) mb;\n"
      "  real r;\n"
      "  initial begin\n"
      "    mb.put(r);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §15.4.9: the compile-time check applies wherever a parameterized-mailbox
// method call appears, not only in an initial block. A mismatched put() inside
// a task body is rejected too — a distinct procedural position from the cases
// above.
TEST(MailboxParameterizedElaborator, MismatchedPutInTaskBodyRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  string s;\n"
      "  task do_send;\n"
      "    mb.put(s);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
