#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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
// either a sequence expression or a multiclock sequence expression, held apart
// from the declaration's children.
TEST(SequenceDeclModel, BodyExprReachesSequenceExprOrMulticlock) {
  VpiObject with_seq;
  with_seq.type = vpiSequenceDecl;
  VpiObject seq;
  seq.type = vpiSequenceInst;  // a sequence-expr kind (see §37.54)
  with_seq.body = &seq;
  EXPECT_EQ(VpiSeqDeclBodyExpr(&with_seq), &seq);

  VpiObject with_multiclock;
  with_multiclock.type = vpiSequenceDecl;
  VpiObject mc;
  mc.type = vpiMulticlockSequenceExpr;
  with_multiclock.body = &mc;
  EXPECT_EQ(VpiSeqDeclBodyExpr(&with_multiclock), &mc);

  VpiObject bodiless;
  bodiless.type = vpiSequenceDecl;
  VpiObject variable;
  variable.type = vpiIntVar;  // a variable it declares is not its body
  bodiless.children = {&variable};
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

// Diagram (sequence decl -> name: str vpiName, str vpiFullName; seq formal decl
// -> name: str vpiName): a sequence declaration reports both a simple name and
// a full name through vpi_get_str(), and a sequence formal reports its simple
// name. The full-name query falls back to the simple name when none is stored.
TEST(SequenceDeclModel, SequenceDeclAndFormalReportTheirNames) {
  VpiContext ctx;
  VpiObject decl;
  decl.type = vpiSequenceDecl;
  decl.name = "req_ack";
  decl.full_name = "top.req_ack";
  EXPECT_STREQ(ctx.GetStr(vpiName, &decl), "req_ack");
  EXPECT_STREQ(ctx.GetStr(vpiFullName, &decl), "top.req_ack");

  VpiObject formal;
  formal.type = vpiSeqFormalDecl;
  formal.name = "win";
  EXPECT_STREQ(ctx.GetStr(vpiName, &formal), "win");
  // No full name stored on the formal -> the full-name query falls back to the
  // simple name.
  EXPECT_STREQ(ctx.GetStr(vpiFullName, &formal), "win");
}

// §37.53 detail 2: a formal's typespec is its typespec child, found past a
// child of another kind.
TEST(SequenceFormal, TypespecFoundPastOtherChildren) {
  VpiObject attribute;
  attribute.type = vpiAttribute;
  VpiObject typespec;
  typespec.type = vpiTypespec;
  VpiObject formal;
  formal.type = vpiSeqFormalDecl;
  formal.children = {&attribute, &typespec};
  EXPECT_EQ(VpiSeqFormalTypespec(&formal), &typespec);
}

// The sequence decls of a run: those a design's scopes declare, built from the
// elaborated design rather than by hand (#7037).
class SequenceDeclsOfARun : public VpiDesignRun {
 protected:
  // The kind of what `relation` reaches from `ref`, 0 for nothing.
  static int KindReached(int relation, vpiHandle ref) {
    vpiHandle reached = ref == nullptr ? nullptr : vpi_handle(relation, ref);
    return reached == nullptr ? 0 : vpi_get(vpiType, reached);
  }

  // The names of the objects of `type` `ref` reaches, in the order reached.
  static std::vector<std::string> OrderedNamesOf(int type, vpiHandle ref) {
    std::vector<std::string> names;
    for (vpiHandle obj : ObjectsOf(type, ref)) {
      names.emplace_back(vpi_get_str(vpiName, obj));
    }
    return names;
  }

  // The kinds of the objects named `name` that `from` reaches, itself
  // included, through operands, match items and an assignment's right side,
  // at any depth, in the order reached.
  static std::vector<int> KindsNamed(vpiHandle from, const std::string& name) {
    std::vector<int> kinds;
    if (from == nullptr) return kinds;
    const char* own = vpi_get_str(vpiName, from);
    if (own != nullptr && name == own) kinds.push_back(vpi_get(vpiType, from));
    const auto kAdd = [&kinds](const std::vector<int>& more) {
      kinds.insert(kinds.end(), more.begin(), more.end());
    };
    for (int relation : {vpiOperand, vpiMatchItem}) {
      for (vpiHandle reached : ObjectsOf(relation, from)) {
        kAdd(KindsNamed(reached, name));
      }
    }
    kAdd(KindsNamed(vpi_handle(vpiRhs, from), name));
    return kinds;
  }
};

// A sequence a module declares is a sequence decl of its instance, named in
// it, reaching its formals in the order declared (detail 1), each of no
// direction unless it is a local variable argument (detail 4), the typespec
// of a typed one and none for an untyped one (detail 2), and a default value
// through vpiExpr (detail 3). The local variable argument is written last,
// as §16.8.2 carries `local` on to the formals after it.
TEST_F(SequenceDeclsOfARun, AnInstanceReachesTheSequenceItDeclares) {
  Run("module top; logic clk, a, b;\n"
      "  sequence s(x, untyped y = b, bit z, local input int n);\n"
      "    a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiSequenceDecl, By("top"), "s");
  ASSERT_NE(decl, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, decl), "top.s");
  EXPECT_EQ(OrderedNamesOf(vpiSeqFormalDecl, decl),
            (std::vector<std::string>{"x", "y", "z", "n"}));
  vpiHandle x = Named(vpiSeqFormalDecl, decl, "x");
  vpiHandle n = Named(vpiSeqFormalDecl, decl, "n");
  vpiHandle y = Named(vpiSeqFormalDecl, decl, "y");
  vpiHandle z = Named(vpiSeqFormalDecl, decl, "z");
  ASSERT_NE(x, nullptr);
  ASSERT_NE(n, nullptr);
  ASSERT_NE(y, nullptr);
  ASSERT_NE(z, nullptr);
  EXPECT_EQ(vpi_get(vpiDirection, x), vpiNoDirection);
  EXPECT_EQ(vpi_get(vpiDirection, n), vpiInput);
  EXPECT_EQ(vpi_get(vpiDirection, y), vpiNoDirection);
  EXPECT_EQ(KindReached(vpiTypespec, x), 0);
  EXPECT_EQ(KindReached(vpiTypespec, n), vpiIntTypespec);
  EXPECT_EQ(KindReached(vpiTypespec, y), 0);
  EXPECT_EQ(KindReached(vpiTypespec, z), vpiBitTypespec);
  vpiHandle value = vpi_handle(vpiExpr, y);
  ASSERT_NE(value, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, value), "b");
  EXPECT_EQ(vpi_handle(vpiExpr, x), nullptr);
}

// Detail 2 with §37.25: a formal of a packed type reaches a typespec of its
// keyword with the range it was written with, as does a formal it carries its
// type on to (§16.8); one of a user-defined type the typespec of the typedef
// naming it, the module's or the compilation unit's; and one of the sequence
// type a sequence typespec.
TEST_F(SequenceDeclsOfARun, AFormalOfAWrittenTypeReachesItsTypespec) {
  Run("typedef logic [7:0] byte_t;\n"
      "module top; logic a, b;\n"
      "  typedef struct packed { logic a, b; } pair_t;\n"
      "  sequence s(bit [3:0] v, u, pair_t t, byte_t w, sequence q);\n"
      "    a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiSequenceDecl, By("top"), "s");
  ASSERT_NE(decl, nullptr);
  // The size of the first range of the typespec `formal` reaches, 0 for none.
  const auto kRangeSizeOf = [decl](const char* formal) {
    vpiHandle ts =
        vpi_handle(vpiTypespec, Named(vpiSeqFormalDecl, decl, formal));
    vpiHandle ranges = ts == nullptr ? nullptr : vpi_iterate(vpiRange, ts);
    vpiHandle range = ranges == nullptr ? nullptr : vpi_scan(ranges);
    return range == nullptr ? 0 : vpi_get(vpiSize, range);
  };
  EXPECT_EQ(KindReached(vpiTypespec, Named(vpiSeqFormalDecl, decl, "v")),
            vpiBitTypespec);
  EXPECT_EQ(kRangeSizeOf("v"), 4);
  EXPECT_EQ(KindReached(vpiTypespec, Named(vpiSeqFormalDecl, decl, "u")),
            vpiBitTypespec);
  EXPECT_EQ(kRangeSizeOf("u"), 4);
  vpiHandle t = vpi_handle(vpiTypespec, Named(vpiSeqFormalDecl, decl, "t"));
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(vpi_get(vpiType, t), vpiStructTypespec);
  EXPECT_STREQ(vpi_get_str(vpiName, t), "pair_t");
  vpiHandle w = vpi_handle(vpiTypespec, Named(vpiSeqFormalDecl, decl, "w"));
  ASSERT_NE(w, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, w), "byte_t");
  EXPECT_EQ(KindReached(vpiTypespec, Named(vpiSeqFormalDecl, decl, "q")),
            vpiSequenceTypespec);
}

// Detail 2 with §26.3: a formal of a package's type, pk::t, reaches the
// package's typespec for it, not the compilation unit's of the same name
// (#7306).
TEST_F(SequenceDeclsOfARun, AFormalOfAPackagesTypeReachesItsTypespec) {
  Run("typedef bit [5:0] t;\n"
      "package pk; typedef logic [1:0] t; endpackage\n"
      "module top; logic a;\n"
      "  sequence s(pk::t x); a ##1 x[0]; endsequence\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiSequenceDecl, By("top"), "s");
  ASSERT_NE(decl, nullptr);
  vpiHandle x = vpi_handle(vpiTypespec, Named(vpiSeqFormalDecl, decl, "x"));
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(vpi_compare_objects(x, Named(vpiTypedef, By("pk"), "t")));
}

// Detail 2 and §37.51 detail 3 with §8.23 and §8.25: a sequence or property
// formal of a class's type, C#(8)::t, reaches a typespec of the type the
// typedef stands for under the specialization, as does a formal it carries
// its type on to (§16.8), and one of an unparameterized class's, D::u, the
// typedef's type; one of an array typedef is not taken for its element type
// (#7307).
TEST_F(SequenceDeclsOfARun, AFormalOfAClassesTypeReachesTheTypedefsType) {
  Run("class C #(int W = 1);\n"
      "  typedef logic [W-1:0] t; typedef logic [W-1:0] arr_t [2];\n"
      "endclass\n"
      "class D; typedef bit [2:0] u; endclass\n"
      "module top; logic a, clk;\n"
      "  sequence s(C#(8)::t x, y, D::u z, C#(2)::arr_t w);\n"
      "    a ##1 x[0];\n"
      "  endsequence\n"
      "  property p(C#(8)::t v); @(posedge clk) v[0]; endproperty\n"
      "endmodule\n");
  vpiHandle seq = Named(vpiSequenceDecl, By("top"), "s");
  vpiHandle prop = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(seq, nullptr);
  ASSERT_NE(prop, nullptr);
  // The kind of the typespec `formal` reaches and the size of its first
  // range, 0 for none.
  const auto kKindAndSize = [](vpiHandle formal) {
    vpiHandle ts = vpi_handle(vpiTypespec, formal);
    vpiHandle ranges = ts == nullptr ? nullptr : vpi_iterate(vpiRange, ts);
    vpiHandle range = ranges == nullptr ? nullptr : vpi_scan(ranges);
    return std::vector<int>{ts == nullptr ? 0 : vpi_get(vpiType, ts),
                            range == nullptr ? 0 : vpi_get(vpiSize, range)};
  };
  const std::vector<int> kLogic8{vpiLogicTypespec, 8};
  EXPECT_EQ(kKindAndSize(Named(vpiSeqFormalDecl, seq, "x")), kLogic8);
  EXPECT_EQ(kKindAndSize(Named(vpiSeqFormalDecl, seq, "y")), kLogic8);
  EXPECT_EQ(kKindAndSize(Named(vpiSeqFormalDecl, seq, "z")),
            (std::vector<int>{vpiBitTypespec, 3}));
  EXPECT_NE(kKindAndSize(Named(vpiSeqFormalDecl, seq, "w"))[0],
            vpiLogicTypespec);
  EXPECT_EQ(kKindAndSize(Named(vpiPropFormalDecl, prop, "v")), kLogic8);
}

// Detail 2 and §37.51 detail 3 with §7.4.4 and §37.25 detail 8: a formal of
// a class's typedef writing an unpacked dimension, C#(2)::arr_t or D::u,
// reaches an array typespec ranging over that dimension, its element typespec
// the typedef's packed type under the specialization (#7309).
TEST_F(SequenceDeclsOfARun, AFormalOfAClassesArrayTypedefIsAnArray) {
  Run("class C #(int W = 1); typedef logic [W-1:0] arr_t [2]; endclass\n"
      "class D; typedef bit [2:0] u [2]; endclass\n"
      "module top; logic a, clk;\n"
      "  sequence s(C#(2)::arr_t w, D::u z); a ##1 a; endsequence\n"
      "  property p(D::u v); @(posedge clk) a; endproperty\n"
      "endmodule\n");
  vpiHandle seq = Named(vpiSequenceDecl, By("top"), "s");
  vpiHandle prop = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(seq, nullptr);
  ASSERT_NE(prop, nullptr);
  // The kind of `ts` and the size of its first range, 0 for none.
  const auto kKindAndSize = [](vpiHandle ts) {
    vpiHandle ranges = ts == nullptr ? nullptr : vpi_iterate(vpiRange, ts);
    vpiHandle range = ranges == nullptr ? nullptr : vpi_scan(ranges);
    return std::vector<int>{ts == nullptr ? 0 : vpi_get(vpiType, ts),
                            range == nullptr ? 0 : vpi_get(vpiSize, range)};
  };
  // The kind and first range size of the typespec `formal` reaches, then of
  // the element typespec that one reaches.
  const auto kShape = [&](vpiHandle formal) {
    vpiHandle ts = vpi_handle(vpiTypespec, formal);
    std::vector<int> shape = kKindAndSize(ts);
    const std::vector<int> kElem =
        kKindAndSize(ts == nullptr ? nullptr : vpi_handle(vpiElemTypespec, ts));
    shape.insert(shape.end(), kElem.begin(), kElem.end());
    return shape;
  };
  const std::vector<int> kBits{vpiArrayTypespec, 2, vpiBitTypespec, 3};
  EXPECT_EQ(kShape(Named(vpiSeqFormalDecl, seq, "w")),
            (std::vector<int>{vpiArrayTypespec, 2, vpiLogicTypespec, 2}));
  EXPECT_EQ(kShape(Named(vpiSeqFormalDecl, seq, "z")), kBits);
  EXPECT_EQ(kShape(Named(vpiPropFormalDecl, prop, "v")), kBits);
}

// Detail 2 with §37.25 detail 2 and §7.8: a formal of a class's typedef of
// an associative array reaches an array typespec of that kind whose index
// typespec is the index type's: a keyword's own, or the typespec the
// compilation unit's typedef of that name declares (#7319).
TEST_F(SequenceDeclsOfARun, AFormalOfAClassesAssocTypedefReachesItsIndex) {
  Run("typedef int idx_t;\n"
      "class D; typedef bit [2:0] m_t [int]; typedef logic n_t [idx_t];\n"
      "endclass\n"
      "module top; logic a;\n"
      "  sequence s(D::m_t z, D::n_t n); a ##1 a; endsequence\n"
      "endmodule\n");
  vpiHandle seq = Named(vpiSequenceDecl, By("top"), "s");
  ASSERT_NE(seq, nullptr);
  vpiHandle z = vpi_handle(vpiTypespec, Named(vpiSeqFormalDecl, seq, "z"));
  vpiHandle n = vpi_handle(vpiTypespec, Named(vpiSeqFormalDecl, seq, "n"));
  ASSERT_NE(z, nullptr);
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(vpi_get(vpiType, z), vpiArrayTypespec);
  EXPECT_EQ(vpi_get(vpiArrayType, z), vpiAssocArray);
  vpiHandle index = vpi_handle(vpiIndexTypespec, z);
  ASSERT_NE(index, nullptr);
  EXPECT_EQ(vpi_get(vpiType, index), vpiIntTypespec);
  vpiHandle elem = vpi_handle(vpiElemTypespec, z);
  ASSERT_NE(elem, nullptr);
  EXPECT_EQ(vpi_get(vpiType, elem), vpiBitTypespec);
  EXPECT_EQ(vpi_get(vpiArrayType, n), vpiAssocArray);
  vpiHandle named = vpi_handle(vpiIndexTypespec, n);
  ASSERT_NE(named, nullptr);
  EXPECT_EQ(vpi_get(vpiType, named), vpiIntTypespec);
  EXPECT_STREQ(vpi_get_str(vpiName, named), "idx_t");
}

// §16.8 and §16.8.2 with §37.15: a sequence body naming its formals reaches
// a ref obj named after each formal it references, bound to no actual since
// no instance binds one there (detail 3), and a variable of the formal's type
// for each local variable formal, a keyword's or the one a type name stands
// for; a package's sequence alike (#7303).
TEST_F(SequenceDeclsOfARun, ABodyReachesItsFormalsAsRefObjsAndVariables) {
  Run("package pk; sequence ps(x); x; endsequence endpackage\n"
      "module top; logic a;\n"
      "  typedef logic [1:0] nib_t;\n"
      "  sequence s(x, local input int n, local input nib_t m);\n"
      "    (a, n = n + 1, m = m) ##1 x;\n"
      "  endsequence\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiSequenceDecl, By("top"), "s");
  ASSERT_NE(decl, nullptr);
  vpiHandle body = vpi_handle(vpiExpr, decl);
  EXPECT_EQ(KindsNamed(body, "x"), (std::vector<int>{vpiRefObj}));
  EXPECT_EQ(KindsNamed(body, "n"), (std::vector<int>{vpiIntVar}));
  EXPECT_EQ(KindsNamed(body, "m"), (std::vector<int>{vpiLogicVar}));
  vpiHandle in_package =
      vpi_handle(vpiExpr, Named(vpiSequenceDecl, By("pk"), "ps"));
  ASSERT_NE(in_package, nullptr);
  EXPECT_EQ(vpi_get(vpiType, in_package), vpiRefObj);
  EXPECT_STREQ(vpi_get_str(vpiName, in_package), "x");
  EXPECT_EQ(vpi_handle(vpiActual, in_package), nullptr);
}

// Detail 4: a local variable argument written as an output or an inout has
// that direction (§16.8.2).
TEST_F(SequenceDeclsOfARun, AnOutputAndAnInoutFormalHaveTheirDirections) {
  Run("module top; logic a;\n"
      "  sequence s(local inout int x, local output int y);\n"
      "    (a, x += 1, y = 2);\n"
      "  endsequence\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiSequenceDecl, By("top"), "s");
  ASSERT_NE(decl, nullptr);
  vpiHandle x = Named(vpiSeqFormalDecl, decl, "x");
  vpiHandle y = Named(vpiSeqFormalDecl, decl, "y");
  ASSERT_NE(x, nullptr);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(vpi_get(vpiDirection, x), vpiInout);
  EXPECT_EQ(vpi_get(vpiDirection, y), vpiOutput);
}

// A sequence reaches the local variables it declares (§16.10), each of the
// kind its type is, and through vpiExpr its body: a sequence expr where it
// opens with no clock, where it opens with one a multiclock sequence expr
// holding the clocked seq of that clock and the body, and where its operands
// name clocks a clocked seq per run of operands on one clock (§37.56).
TEST_F(SequenceDeclsOfARun, ASequenceReachesItsVariablesAndItsBody) {
  Run("module top; logic clk, a, b;\n"
      "  sequence s1;\n"
      "    int m;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  sequence s2; a ##[1:2] b; endsequence\n"
      "  sequence s3; @(posedge clk) a ##1 @(negedge clk) b; endsequence\n"
      "endmodule\n");
  vpiHandle s1 = Named(vpiSequenceDecl, By("top"), "s1");
  vpiHandle s2 = Named(vpiSequenceDecl, By("top"), "s2");
  ASSERT_NE(s1, nullptr);
  ASSERT_NE(s2, nullptr);
  EXPECT_EQ(OrderedNamesOf(vpiVariables, s1), (std::vector<std::string>{"m"}));
  EXPECT_EQ(KindsOf(vpiVariables, s1), (std::vector<int>{vpiIntVar}));
  EXPECT_EQ(FullNameOfChild(s1, "m"), "top.s1.m");
  vpiHandle multiclock = vpi_handle(vpiExpr, s1);
  ASSERT_NE(multiclock, nullptr);
  EXPECT_EQ(vpi_get(vpiType, multiclock), vpiMulticlockSequenceExpr);
  const std::vector<vpiHandle> kClocked = ObjectsOf(vpiClockedSeq, multiclock);
  ASSERT_EQ(kClocked.size(), 1U);
  vpiHandle clock = vpi_handle(vpiClockingEvent, kClocked[0]);
  ASSERT_NE(clock, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, clock), vpiPosedgeOp);
  EXPECT_EQ(OpOf(vpi_handle(vpiOperation, kClocked[0])), vpiCycleDelayOp);
  EXPECT_EQ(OpOf(vpi_handle(vpiExpr, s2)), vpiCycleDelayOp);
  EXPECT_TRUE(ObjectsOf(vpiVariables, s2).empty());
  vpiHandle runs = vpi_handle(vpiExpr, Named(vpiSequenceDecl, By("top"), "s3"));
  ASSERT_NE(runs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, runs), vpiMulticlockSequenceExpr);
  const std::vector<vpiHandle> kRuns = ObjectsOf(vpiClockedSeq, runs);
  ASSERT_EQ(kRuns.size(), 2U);
  const auto kEdgeOf = [](vpiHandle clocked) {
    vpiHandle event = vpi_handle(vpiClockingEvent, clocked);
    return event == nullptr ? 0 : vpi_get(vpiOpType, event);
  };
  EXPECT_EQ(kEdgeOf(kRuns[0]), vpiPosedgeOp);
  EXPECT_EQ(kEdgeOf(kRuns[1]), vpiNegedgeOp);
}

// A sequence a generate block declares is one of that block's instance, and
// one a clocking block declares is one of that block (§37.12, §27.4, §14.3).
TEST_F(SequenceDeclsOfARun, AGenerateAndAClockingBlockReachTheirSequences) {
  Run("module top; logic clk, a;\n"
      "  for (genvar i = 0; i < 1; i++) begin : g\n"
      "    sequence s; a; endsequence\n"
      "  end\n"
      "  clocking cb @(posedge clk);\n"
      "    sequence cs; a; endsequence\n"
      "  endclocking\n"
      "endmodule\n");
  vpiHandle in_block = Named(vpiSequenceDecl, By("top.g[0]"), "s");
  ASSERT_NE(in_block, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, in_block), "top.g[0].s");
  EXPECT_EQ(Named(vpiSequenceDecl, By("top"), "s"), nullptr);
  vpiHandle cb = Named(vpiClockingBlock, By("top"), "cb");
  ASSERT_NE(cb, nullptr);
  vpiHandle in_clocking = Named(vpiSequenceDecl, cb, "cs");
  ASSERT_NE(in_clocking, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, in_clocking), "top.cb.cs");
}

// A sequence a package declares is a sequence decl of the package, and a
// property of the package naming it, bare or called, reaches its sequence
// inst (§37.10 detail 1, §37.54), elaboration having written each name the
// package's declarations read through the package's path (§26.3).
TEST_F(SequenceDeclsOfARun, APackageReachesTheSequenceItDeclares) {
  Run("package pk; logic x;\n"
      "  sequence ps; x; endsequence\n"
      "  sequence pc(v); v; endsequence\n"
      "  property pp; ps; endproperty\n"
      "  property pq; pc(x); endproperty\n"
      "endpackage\n"
      "module top; endmodule\n");
  vpiHandle pkg = By("pk");
  ASSERT_NE(pkg, nullptr);
  vpiHandle decl = Named(vpiSequenceDecl, pkg, "ps");
  ASSERT_NE(decl, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, decl), "pk::ps");
  vpiHandle body = vpi_handle(vpiExpr, decl);
  ASSERT_NE(body, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, body), "x");
  vpiHandle property = Named(vpiPropertyDecl, pkg, "pp");
  ASSERT_NE(property, nullptr);
  vpiHandle spec = vpi_handle(vpiPropertySpec, property);
  ASSERT_NE(spec, nullptr);
  vpiHandle inst = vpi_handle(vpiPropertyExpr, spec);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(vpi_get(vpiType, inst), vpiSequenceInst);
  EXPECT_TRUE(vpi_compare_objects(vpi_handle(vpiSequenceDecl, inst), decl));
  vpiHandle called = vpi_handle(
      vpiPropertyExpr,
      vpi_handle(vpiPropertySpec, Named(vpiPropertyDecl, pkg, "pq")));
  ASSERT_NE(called, nullptr);
  EXPECT_EQ(vpi_get(vpiType, called), vpiSequenceInst);
  EXPECT_TRUE(vpi_compare_objects(vpi_handle(vpiSequenceDecl, called),
                                  Named(vpiSequenceDecl, pkg, "pc")));
  EXPECT_EQ(NamesOf(vpiArgument, called), (std::vector<std::string>{"x"}));
}

}  // namespace
}  // namespace delta
