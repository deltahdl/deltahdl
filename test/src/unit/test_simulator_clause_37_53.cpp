#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.53 sequence declaration: the VPI object model for a sequence declaration
// and its formals. A sequence declaration's formals are returned in declaration
// order; each formal exposes a direction, an optional typespec, and an optional
// initialization expression; the declaration's body is reached through vpiExpr
// as either a sequence expression or a multiclock sequence expression. The
// argument and initialization-expression kinds reuse §37.54's sequence-expr
// classification. These tests observe the production helpers in vpi.cpp and the
// VpiContext iteration that apply those rules.

// Detail 1: the vpiSeqFormalDecl iteration returns a sequence declaration's
// formals in declaration order; both the dedicated helper and the generic
// iteration observe the same ordered formals and skip non-formal members.
TEST(SequenceDeclModel, SeqFormalDeclIterationFollowsDeclarationOrder) {
  VpiContext ctx;
  VpiObject decl;
  decl.type = vpiSequenceDecl;
  VpiObject body;
  body.type = vpiSequenceInst;  // a body member, not a formal
  VpiObject f0;
  f0.type = vpiSeqFormalDecl;
  VpiObject f1;
  f1.type = vpiSeqFormalDecl;
  decl.children = {&f0, &body, &f1};

  auto formals = VpiSeqFormals(&decl);
  ASSERT_EQ(formals.size(), 2u);
  EXPECT_EQ(formals[0], &f0);
  EXPECT_EQ(formals[1], &f1);

  VpiHandle it = ctx.Iterate(vpiSeqFormalDecl, &decl);
  ASSERT_NE(it, nullptr);
  std::vector<VpiHandle> seen;
  while (VpiHandle h = ctx.Scan(it)) seen.push_back(h);
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], &f0);
  EXPECT_EQ(seen[1], &f1);
}

// Detail 1 edge: a null handle declares no formals.
TEST(SequenceDeclModel, NullDeclarationHasNoFormals) {
  EXPECT_TRUE(VpiSeqFormals(nullptr).empty());
}

// Diagram (sequence decl -- vpiExpr --> sequence expr | multiclock sequence
// expr): the body of a sequence declaration is reached through vpiExpr and is
// either a sequence expression or a multiclock sequence expression.
TEST(SequenceDeclModel, BodyExprReachesSequenceExprOrMulticlock) {
  VpiObject with_seq;
  with_seq.type = vpiSequenceDecl;
  VpiObject seq;
  seq.type = vpiSequenceInst;  // a sequence-expr kind (see §37.54)
  with_seq.children = {&seq};
  EXPECT_EQ(VpiSeqDeclBodyExpr(&with_seq), &seq);

  VpiObject with_multiclock;
  with_multiclock.type = vpiSequenceDecl;
  VpiObject mc;
  mc.type = vpiMulticlockSequenceExpr;
  with_multiclock.children = {&mc};
  EXPECT_EQ(VpiSeqDeclBodyExpr(&with_multiclock), &mc);

  VpiObject bodiless;
  bodiless.type = vpiSequenceDecl;
  VpiObject formal;
  formal.type = vpiSeqFormalDecl;  // a formal is not a body expression
  bodiless.children = {&formal};
  EXPECT_EQ(VpiSeqDeclBodyExpr(&bodiless), nullptr);
  EXPECT_EQ(VpiSeqDeclBodyExpr(nullptr), nullptr);
}

// Detail 2: the vpiTypespec relation returns the formal's typespec when typed
// and null when the formal is untyped.
TEST(SequenceDeclModel, FormalTypespecReportsNullWhenUntyped) {
  VpiObject typed;
  typed.type = vpiSeqFormalDecl;
  VpiObject ts;
  ts.type = vpiTypespec;
  typed.children = {&ts};
  EXPECT_EQ(VpiSeqFormalTypespec(&typed), &ts);

  VpiObject untyped;
  untyped.type = vpiSeqFormalDecl;
  EXPECT_EQ(VpiSeqFormalTypespec(&untyped), nullptr);
  EXPECT_EQ(VpiSeqFormalTypespec(nullptr), nullptr);
}

// Detail 3: a formal's initialization expression is reached through vpiExpr;
// the diagram draws its target as a named event or a sequence expression, and a
// formal with no initialization expression reports none.
TEST(SequenceDeclModel, FormalInitExprReachesNamedEventOrSequenceExpr) {
  VpiObject with_event;
  with_event.type = vpiSeqFormalDecl;
  VpiObject ev;
  ev.type = vpiNamedEvent;
  with_event.children = {&ev};
  EXPECT_EQ(VpiSeqFormalInitExpr(&with_event), &ev);

  VpiObject with_seq_expr;
  with_seq_expr.type = vpiSeqFormalDecl;
  VpiObject se;
  se.type =
      vpiConstant;  // a sequence-expr kind (a bare expression, see §37.54)
  with_seq_expr.children = {&se};
  EXPECT_EQ(VpiSeqFormalInitExpr(&with_seq_expr), &se);

  VpiObject typed_only;
  typed_only.type = vpiSeqFormalDecl;
  VpiObject ts;
  ts.type = vpiTypespec;  // a typespec is not an initialization expression
  typed_only.children = {&ts};
  EXPECT_EQ(VpiSeqFormalInitExpr(&typed_only), nullptr);
  EXPECT_EQ(VpiSeqFormalInitExpr(nullptr), nullptr);
}

// Detail 4: vpiDirection is vpiNoDirection for a formal that is not a local
// variable argument; a local variable argument reports its declared direction,
// which is one of vpiInput, vpiOutput, or vpiInout. (Unlike §37.51's property
// formal, a sequence formal may be an output or inout, not only an input.)
TEST(SequenceDeclModel, FormalDirectionSpansInputOutputInoutForLocalVariables) {
  // A non-local-variable formal has no direction, whatever value is passed for
  // the declared direction.
  EXPECT_EQ(VpiSeqFormalDirection(false, vpiInput), vpiNoDirection);
  EXPECT_EQ(VpiSeqFormalDirection(false, vpiOutput), vpiNoDirection);
  EXPECT_EQ(VpiSeqFormalDirection(false, vpiInout), vpiNoDirection);

  // A local variable argument reports its declared direction, any of the three.
  EXPECT_EQ(VpiSeqFormalDirection(true, vpiInput), vpiInput);
  EXPECT_EQ(VpiSeqFormalDirection(true, vpiOutput), vpiOutput);
  EXPECT_EQ(VpiSeqFormalDirection(true, vpiInout), vpiInout);
}

}  // namespace
}  // namespace delta
