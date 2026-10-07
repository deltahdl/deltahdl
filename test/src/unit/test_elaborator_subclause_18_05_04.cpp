#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// These tests observe the elaborator rule of 18.5.4 (and its footnote 13): the
// range_list of a uniqueness constraint shall contain only expressions that
// denote singular or array variables. The rule is about what an operand
// denotes, so it lives at the elaborator stage; the parser accepts the
// range_list tokens regardless. Each program is built from real class source so
// the check runs over the elaborated constraint, not a hand-built state.

// 18.5.4: a group of singular variables denotes variables and is accepted.
TEST(UniqueMemberForms, SingularVariableGroupAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand byte a;\n"
             "  rand byte b;\n"
             "  rand byte excluded;\n"
             "  constraint u { unique {a, b, excluded}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.4: a slice of an unpacked array denotes an array variable, so a group
// mixing a slice with singular variables (the unique {b, a[2:3], excluded}
// example) is accepted.
TEST(UniqueMemberForms, ArraySliceMemberAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand byte a[5];\n"
             "  rand byte b;\n"
             "  rand byte excluded;\n"
             "  constraint u { unique {b, a[2:3], excluded}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.4 / footnote 13: a range_list member shall denote a variable. A literal
// denotes no variable, so a group naming one is rejected.
TEST(UniqueMemberForms, LiteralMemberRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand byte a;\n"
             "  constraint u { unique {a, 5}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a uniqueness constraint member shall denote a "
                            "singular or array variable",
                            3, "18.5.4"));
}

// 18.5.4 / footnote 13: an arithmetic expression is not a variable reference,
// so a group naming one is rejected.
TEST(UniqueMemberForms, ArithmeticExpressionMemberRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand byte a;\n"
             "  rand byte b;\n"
             "  constraint u { unique {a + b}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a uniqueness constraint member shall denote a "
                            "singular or array variable",
                            4, "18.5.4"));
}

// 18.5.4: a singular member may be of real type as well as integral, so a group
// of real variables denotes variables and is accepted — the admitted-operand
// form exercised here is the real singular variable.
TEST(UniqueMemberForms, SingularRealVariableGroupAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand real a;\n"
             "  rand real b;\n"
             "  constraint u { unique {a, b}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.4: a whole unpacked array variable (not only a slice of one) is an
// admitted member form, so a group naming an array beside a singular variable
// is accepted.
TEST(UniqueMemberForms, WholeUnpackedArrayMemberAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand byte a[5];\n"
             "  rand byte b;\n"
             "  constraint u { unique {a, b}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.4 / footnote 13: a member/scope-qualified reference still denotes a
// variable. A group written with the explicit object handle (this.x) is
// accepted — this exercises the member-access member form, a distinct path from
// a bare identifier or an array select.
TEST(UniqueMemberForms, QualifiedMemberReferenceAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand byte a;\n"
             "  rand byte b;\n"
             "  constraint u { unique {this.a, this.b}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.4: each member of a uniqueness group has an integral or real type. A
// string variable is plainly neither, so a group naming one is rejected even
// though the string does denote a variable.
TEST(UniqueMemberForms, NonIntegralNonRealMemberRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int a;\n"
             "  string s;\n"
             "  constraint u { unique {a, s}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a uniqueness constraint member shall be of "
                            "integral or real type",
                            4, "18.5.4"));
}

// 18.5.4: a uniqueness group admits no randc variable, so a group naming a
// randc variable beside a rand one is rejected at the randc member.
TEST(UniqueMemberForms, RandcMemberRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  randc bit [1:0] a;\n"
             "  rand bit [1:0] b;\n"
             "  constraint u { unique {b, a}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a uniqueness constraint member shall not be "
                            "a randc variable",
                            4, "18.5.4"));
}

// 18.5.4: an inherited randc variable is as much a randc variable of the
// group as one the class declares itself.
TEST(UniqueMemberForms, InheritedRandcMemberRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class B;\n"
             "  randc bit [2:0] a;\n"
             "endclass\n"
             "class C extends B;\n"
             "  rand bit [2:0] b[2];\n"
             "  constraint u { unique {b, a}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a uniqueness constraint member shall not be "
                            "a randc variable",
                            6, "18.5.4"));
}

// 18.5.4 with 18.7: an inline constraint block holds a uniqueness constraint as
// a class's constraint block does, so the ban on a randc member reaches the
// group of randomize() with called through a handle in a module, whether the
// handle is declared in the module or in the procedure.
TEST(UniqueMemberForms, InlineRandcMemberThroughHandleRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "module m;\n"
             "  C c = new;\n"
             "  initial begin\n"
             "    C d;\n"
             "    d = new;\n"
             "    void'(c.randomize() with { unique {a, b}; });\n"
             "    void'(d.randomize() with { unique {b, a}; });\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a uniqueness constraint member shall not be a randc variable", 10,
      "18.5.4"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a uniqueness constraint member shall not be a randc variable", 11,
      "18.5.4"));
}

// 18.5.4 with 18.7: the same holds for randomize() with called on the object
// itself in one of its methods, with or without this.
TEST(UniqueMemberForms, InlineRandcMemberInMethodRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "  function int f();\n"
             "    return randomize() with { unique {a, b}; };\n"
             "  endfunction\n"
             "  function int g();\n"
             "    return this.randomize() with { unique {b, a}; };\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a uniqueness constraint member shall not be a randc variable", 5,
      "18.5.4"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a uniqueness constraint member shall not be a randc variable", 8,
      "18.5.4"));
}

// 18.5.4 with 18.7: an inline group of rand members of the receiver's class is
// accepted wherever randomize() with is called.
TEST(UniqueMemberForms, InlineRandMembersAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  rand bit [1:0] b;\n"
             "  function int f();\n"
             "    return randomize() with { unique {a, b}; };\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c = new;\n"
             "  initial void'(c.randomize() with { unique {a, b}; });\n"
             "endmodule\n"));
}

// 18.5.4 with 18.7: the receiver of randomize() with may be any expression
// that yields a handle, and its group is checked against the class of that
// handle: an element of an array of handles, a handle property reached
// through one or more other handles or through its class, and the handle a
// method or a static method returns.
TEST(UniqueMemberForms, InlineRandcMemberThroughReceiverExpressionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "  static C inst;\n"
             "  function C self(); return this; endfunction\n"
             "  static function C make(); return inst; endfunction\n"
             "endclass\n"
             "class W;\n"
             "  C sub;\n"
             "endclass\n"
             "class V;\n"
             "  W w;\n"
             "endclass\n"
             "module m;\n"
             "  C o[2][2];\n"
             "  initial begin\n"
             "    W w;\n"
             "    V vv;\n"
             "    void'(o[0][1].randomize() with { unique {a, b}; });\n"
             "    void'(w.sub.randomize() with { unique {a, b}; });\n"
             "    void'(o[1][0].self().randomize() with { unique {a, b}; });\n"
             "    void'(C::inst.randomize() with { unique {a, b}; });\n"
             "    void'(C::make().randomize() with { unique {a, b}; });\n"
             "    void'(vv.w.sub.randomize() with { unique {a, b}; });\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_EQ(f.diag.ErrorCount(), 6u);
  for (uint32_t line : {19u, 20u, 21u, 22u, 23u, 24u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "a uniqueness constraint member shall not be a randc variable", line,
        "18.5.4"));
  }
}

// 18.5.4 with 18.7: a method of another class may randomize an object through
// a handle of its own -- a local, an argument, a property of its class or of a
// class it extends -- in a class nested in another, and in a body written out
// of the class's block, which names the same members (8.24); a method of a
// subclass may randomize its own object through super.
TEST(UniqueMemberForms, InlineRandcMemberThroughMethodHandleRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "class B;\n"
             "  C inherited;\n"
             "endclass\n"
             "class H extends B;\n"
             "  C p;\n"
             "  extern function int later();\n"
             "  function int go(C arg);\n"
             "    C x;\n"
             "    return x.randomize() with { unique {a, b}; }\n"
             "         + arg.randomize() with { unique {a, b}; }\n"
             "         + p.randomize() with { unique {a, b}; }\n"
             "         + inherited.randomize() with { unique {a, b}; };\n"
             "  endfunction\n"
             "endclass\n"
             "function int H::later();\n"
             "  return p.randomize() with { unique {a, b}; };\n"
             "endfunction\n"
             "class Outer;\n"
             "  class Inner;\n"
             "    function int go(C h);\n"
             "      return h.randomize() with { unique {a, b}; };\n"
             "    endfunction\n"
             "  endclass\n"
             "endclass\n"
             "class E extends C;\n"
             "  function int go();\n"
             "    return super.randomize() with { unique {a, b}; };\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_EQ(f.diag.ErrorCount(), 7u);
  for (uint32_t line : {13u, 14u, 15u, 16u, 20u, 25u, 31u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "a uniqueness constraint member shall not be a randc variable", line,
        "18.5.4"));
  }
}

// 18.5.4 with 18.7: neither clause limits where the call stands, so a call in
// a module's function or task, in a procedure of a generate block, in a
// declaration's initializer or in a package's function is checked as one in
// an initial block is.
TEST(UniqueMemberForms, InlineRandcMemberOutsideModuleProcedureRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "package p;\n"
             "  C g;\n"
             "  function int f();\n"
             "    return g.randomize() with { unique {a, b}; };\n"
             "  endfunction\n"
             "endpackage\n"
             "module m(input logic clk);\n"
             "  C c = new;\n"
             "  int r = c.randomize() with { unique {a, b}; };\n"
             "  function int f(C arg);\n"
             "    return arg.randomize() with { unique {a, b}; };\n"
             "  endfunction\n"
             "  task t();\n"
             "    void'(c.randomize() with { unique {a, b}; });\n"
             "  endtask\n"
             "  if (1) begin : g\n"
             "    C d;\n"
             "    initial void'(d.randomize() with { unique {a, b}; });\n"
             "  end\n"
             "  case (1)\n"
             "    1: begin : k\n"
             "      initial void'(c.randomize() with { unique {a, b}; });\n"
             "    end\n"
             "  endcase\n"
             "endmodule\n",
             f));
  EXPECT_EQ(f.diag.ErrorCount(), 6u);
  for (uint32_t line : {8u, 13u, 15u, 18u, 22u, 26u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "a uniqueness constraint member shall not be a randc variable", line,
        "18.5.4"));
  }
}

// 18.7: the receiver's name resolves in the innermost scope declaring it, so a
// method's local handle of a class whose b is rand hides the module's handle
// of a class whose b is randc, and the group is accepted; a name the method
// does not redeclare still reaches the module's handle.
TEST(UniqueMemberForms, InlineReceiverResolvesInInnermostScope) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "class D;\n"
             "  rand bit [1:0] a;\n"
             "  rand bit [1:0] b;\n"
             "endclass\n"
             "module m;\n"
             "  C x;\n"
             "  C y;\n"
             "  class H;\n"
             "    function int go();\n"
             "      D x;\n"
             "      return x.randomize() with { unique {a, b}; }\n"
             "           + y.randomize() with { unique {a, b}; };\n"
             "    endfunction\n"
             "  endclass\n"
             "endmodule\n",
             f));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a uniqueness constraint member shall not be a randc variable", 16,
      "18.5.4"));
}

// 18.5.4 with 18.12: a group of rand members is accepted whatever the
// receiver -- a handle in another instance, one named upward through its
// module, the handle an array method yields -- and so is a group of the scope
// randomize, whose names are the calling scope's variables, written with or
// without std::.
TEST(UniqueMemberForms, InlineRandGroupAcceptedWhateverTheReceiver) {
  EXPECT_TRUE(
      ElabOk("class D;\n"
             "  rand bit [1:0] a;\n"
             "  rand bit [1:0] b;\n"
             "endclass\n"
             "module child;\n"
             "  D d = new;\n"
             "  initial void'(m.x.randomize() with { unique {a, b}; });\n"
             "endmodule\n"
             "module m;\n"
             "  D x;\n"
             "  D q[$];\n"
             "  bit [1:0] v;\n"
             "  bit [1:0] w;\n"
             "  child u();\n"
             "  initial begin\n"
             "    void'(u.d.randomize() with { unique {a, b}; });\n"
             "    void'(q.pop_front().randomize() with { unique {a, b}; });\n"
             "    void'(std::randomize(v, w) with { unique {v, w}; });\n"
             "    void'(randomize(v, w) with { unique {v, w}; });\n"
             "  end\n"
             "endmodule\n"));
}

// 18.5.4 with 18.7 and 6.18: a typedef of a class names that class, so a
// handle declared through one -- of the compilation unit, through another
// typedef, of a module, or of the class holding the handle -- is a handle of
// that class; a forward typedef of the class leaves a handle declared with the
// class's own name as it was.
TEST(UniqueMemberForms, InlineRandcMemberThroughTypedefHandleRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("typedef class C;\n"
             "class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "typedef C CT;\n"
             "typedef CT CT2;\n"
             "class W;\n"
             "  typedef C T;\n"
             "  T sub;\n"
             "endclass\n"
             "module m;\n"
             "  typedef C MT;\n"
             "  MT y;\n"
             "  initial begin\n"
             "    CT2 x;\n"
             "    W w;\n"
             "    C z;\n"
             "    void'(x.randomize() with { unique {a, b}; });\n"
             "    void'(y.randomize() with { unique {a, b}; });\n"
             "    void'(w.sub.randomize() with { unique {a, b}; });\n"
             "    void'(z.randomize() with { unique {a, b}; });\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
  for (uint32_t line : {19u, 20u, 21u, 22u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "a uniqueness constraint member shall not be a randc variable", line,
        "18.5.4"));
  }
}

// 18.5.4 with 18.7 and 23.6: a hierarchical name reaches a handle in another
// instance -- a child, a child's child, or an element of an array of
// instances -- and the group is checked against that handle's class.
TEST(UniqueMemberForms, InlineRandcMemberThroughInstanceHandleRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "module leaf;\n"
             "  C d;\n"
             "endmodule\n"
             "module mid;\n"
             "  C d;\n"
             "  leaf v();\n"
             "endmodule\n"
             "module m;\n"
             "  mid u();\n"
             "  mid ua[2] ();\n"
             "  initial begin\n"
             "    void'(u.d.randomize() with { unique {a, b}; });\n"
             "    void'(u.v.d.randomize() with { unique {a, b}; });\n"
             "    void'(ua[1].d.randomize() with { unique {a, b}; });\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
  for (uint32_t line : {16u, 17u, 18u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "a uniqueness constraint member shall not be a randc variable", line,
        "18.5.4"));
  }
}

// 18.5.4 with 18.7 and 26.3: a package variable is reached as p::g, or by its
// bare name through a wildcard or an explicit import, and the group is
// checked against its class.
TEST(UniqueMemberForms, InlineRandcMemberThroughPackageHandleRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "package p;\n"
             "  C g;\n"
             "  C h;\n"
             "endpackage\n"
             "package q;\n"
             "  C k;\n"
             "endpackage\n"
             "module m;\n"
             "  import p::*;\n"
             "  import q::k;\n"
             "  initial begin\n"
             "    void'(p::g.randomize() with { unique {a, b}; });\n"
             "    void'(h.randomize() with { unique {a, b}; });\n"
             "    void'(k.randomize() with { unique {a, b}; });\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
  for (uint32_t line : {16u, 17u, 18u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "a uniqueness constraint member shall not be a randc variable", line,
        "18.5.4"));
  }
}

// 18.5.4 with 18.7 and 23.8: a hierarchical name may start with the name of a
// module above, and the group is checked against the class of the handle it
// reaches there. A name a scope declares is that declaration and no module's,
// whether the scope is a class whose property it names or a module whose
// variable a method of a class inside it reads.
TEST(UniqueMemberForms, InlineRandcMemberThroughUpwardReferenceRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "class W;\n"
             "  C sub;\n"
             "endclass\n"
             "module child;\n"
             "  initial void'(t.x.randomize() with { unique {a, b}; });\n"
             "endmodule\n"
             "module t;\n"
             "  C x;\n"
             "  W wm;\n"
             "  child u();\n"
             "  class H;\n"
             "    W own;\n"
             "    function int go();\n"
             "      return own.sub.randomize() with { unique {a, b}; }\n"
             "           + wm.sub.randomize() with { unique {a, b}; };\n"
             "    endfunction\n"
             "  endclass\n"
             "endmodule\n",
             f));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
  for (uint32_t line : {9u, 18u, 19u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "a uniqueness constraint member shall not be a randc variable", line,
        "18.5.4"));
  }
}

// 18.5.4 with 18.7 and 27.6: a named generate block is a scope a hierarchical
// name reaches into -- a conditional block, a case item's block, an element of
// a loop's blocks, or a block inside another instance -- and the group is
// checked against the class of the handle declared there.
TEST(UniqueMemberForms, InlineRandcMemberThroughGenerateBlockHandleRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "module mid;\n"
             "  if (1) begin : gb\n"
             "    C h;\n"
             "  end\n"
             "endmodule\n"
             "module m;\n"
             "  if (1) begin : g\n"
             "    C h;\n"
             "  end else begin : ge\n"
             "    C h;\n"
             "  end\n"
             "  case (1)\n"
             "    1: begin : k\n"
             "      C h;\n"
             "    end\n"
             "  endcase\n"
             "  for (genvar i = 0; i < 2; i++) begin : gl\n"
             "    C h;\n"
             "  end\n"
             "  mid u();\n"
             "  initial begin\n"
             "    void'(g.h.randomize() with { unique {a, b}; });\n"
             "    void'(k.h.randomize() with { unique {a, b}; });\n"
             "    void'(gl[1].h.randomize() with { unique {a, b}; });\n"
             "    void'(u.gb.h.randomize() with { unique {a, b}; });\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
  for (uint32_t line : {26u, 27u, 28u, 29u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "a uniqueness constraint member shall not be a randc variable", line,
        "18.5.4"));
  }
}

// 18.5.4 with 18.7: a receiver whose name resolves to no declaration and no
// module has no class to read the group's names in, so the uniqueness rule
// reports nothing of its own there; resolving the name is left to the rules
// of 23.8.
TEST(UniqueMemberForms, InlineReceiverNamingNothingGetsNoUniquenessReport) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  rand bit [1:0] a;\n"
      "  randc bit [1:0] b;\n"
      "endclass\n"
      "module m;\n"
      "  initial void'(nosuch.x.randomize() with { unique {a, b}; });\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "a uniqueness constraint member shall not be a randc variable", 6,
      "18.5.4"));
}

}  // namespace
