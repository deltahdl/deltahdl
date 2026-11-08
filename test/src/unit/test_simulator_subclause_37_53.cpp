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

TEST(SequenceDeclModel, SeqFormalDeclIterationFollowsDeclarationOrder) {
  VpiContext ctx;
  VpiObject decl;
  decl.type = vpiSequenceDecl;
  VpiObject body;
  body.type = vpiSequenceInst;
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

TEST(SequenceDeclModel, NullDeclarationHasNoFormals) {
  EXPECT_TRUE(VpiSeqFormals(nullptr).empty());
}

TEST(SequenceDeclModel, BodyExprReachesSequenceExprOrMulticlock) {
  VpiObject with_seq;
  with_seq.type = vpiSequenceDecl;
  VpiObject seq;
  seq.type = vpiSequenceInst;
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
  variable.type = vpiIntVar;
  bodiless.children = {&variable};
  EXPECT_EQ(VpiSeqDeclBodyExpr(&bodiless), nullptr);
  EXPECT_EQ(VpiSeqDeclBodyExpr(nullptr), nullptr);
}

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
  se.type = vpiConstant;
  with_seq_expr.children = {&se};
  EXPECT_EQ(VpiSeqFormalInitExpr(&with_seq_expr), &se);

  VpiObject typed_only;
  typed_only.type = vpiSeqFormalDecl;
  VpiObject ts;
  ts.type = vpiTypespec;
  typed_only.children = {&ts};
  EXPECT_EQ(VpiSeqFormalInitExpr(&typed_only), nullptr);
  EXPECT_EQ(VpiSeqFormalInitExpr(nullptr), nullptr);
}

TEST(SequenceDeclModel, FormalDirectionSpansInputOutputInoutForLocalVariables) {
  EXPECT_EQ(VpiSeqFormalDirection(false, vpiInput), vpiNoDirection);
  EXPECT_EQ(VpiSeqFormalDirection(false, vpiOutput), vpiNoDirection);
  EXPECT_EQ(VpiSeqFormalDirection(false, vpiInout), vpiNoDirection);

  EXPECT_EQ(VpiSeqFormalDirection(true, vpiInput), vpiInput);
  EXPECT_EQ(VpiSeqFormalDirection(true, vpiOutput), vpiOutput);
  EXPECT_EQ(VpiSeqFormalDirection(true, vpiInout), vpiInout);
}

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
  EXPECT_STREQ(ctx.GetStr(vpiFullName, &formal), "win");
}

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

class SequenceDeclsOfARun : public VpiDesignRun {
 protected:
  static int KindReached(int relation, vpiHandle ref) {
    vpiHandle reached = ref == nullptr ? nullptr : vpi_handle(relation, ref);
    return reached == nullptr ? 0 : vpi_get(vpiType, reached);
  }

  static std::vector<std::string> OrderedNamesOf(int type, vpiHandle ref) {
    std::vector<std::string> names;
    for (vpiHandle obj : ObjectsOf(type, ref)) {
      names.emplace_back(vpi_get_str(vpiName, obj));
    }
    return names;
  }

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
  const auto kKindAndSize = [](vpiHandle ts) {
    vpiHandle ranges = ts == nullptr ? nullptr : vpi_iterate(vpiRange, ts);
    vpiHandle range = ranges == nullptr ? nullptr : vpi_scan(ranges);
    return std::vector<int>{ts == nullptr ? 0 : vpi_get(vpiType, ts),
                            range == nullptr ? 0 : vpi_get(vpiSize, range)};
  };
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

TEST_F(SequenceDeclsOfARun, APackedLocalHasAVarBitPerBit) {
  Run("module top; logic a;\n"
      "  sequence s;\n"
      "    logic [3:0] v;\n"
      "    bit [0:1] w;\n"
      "    logic g;\n"
      "    (a, v = 4'h5) ##1 v[1];\n"
      "  endsequence\n"
      "  sequence t(local input logic [1:0] n);\n"
      "    a ##1 n[0];\n"
      "  endsequence\n"
      "endmodule\n");
  vpiHandle s = Named(vpiSequenceDecl, By("top"), "s");
  ASSERT_NE(s, nullptr);
  const std::vector<vpiHandle> kLocals = ObjectsOf(vpiVariables, s);
  ASSERT_EQ(kLocals.size(), 3U);
  EXPECT_EQ(OrderedNamesOf(vpiBit, kLocals[0]),
            (std::vector<std::string>{"v[3]", "v[2]", "v[1]", "v[0]"}));
  EXPECT_EQ(KindsOf(vpiBit, kLocals[0]), (std::vector<int>(4, vpiRegBit)));
  EXPECT_EQ(OrderedNamesOf(vpiBit, kLocals[1]),
            (std::vector<std::string>{"w[0]", "w[1]"}));
  EXPECT_TRUE(ObjectsOf(vpiBit, kLocals[2]).empty());
  const std::vector<vpiHandle> kParts = OperandsOf(vpi_handle(vpiExpr, s));
  ASSERT_GE(kParts.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kParts[1]), vpiRegBit);
  EXPECT_STREQ(vpi_get_str(vpiName, kParts[1]), "v[1]");
  EXPECT_NE(vpi_compare_objects(vpi_handle(vpiParent, kParts[1]), kLocals[0]),
            0);
  const std::vector<vpiHandle> kFormalParts =
      OperandsOf(vpi_handle(vpiExpr, Named(vpiSequenceDecl, By("top"), "t")));
  ASSERT_GE(kFormalParts.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kFormalParts[1]), vpiRegBit);
  EXPECT_STREQ(vpi_get_str(vpiName, kFormalParts[1]), "n[0]");
}

TEST_F(SequenceDeclsOfARun, AStructureLocalHasAMemberPerField) {
  Run("module top; logic a;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  typedef struct { nib_t f; int g; } pair_t;\n"
      "  sequence s;\n"
      "    pair_t p;\n"
      "    (a, p.g = 1) ##1 p.g;\n"
      "  endsequence\n"
      "endmodule\n");
  vpiHandle s = Named(vpiSequenceDecl, By("top"), "s");
  ASSERT_NE(s, nullptr);
  const std::vector<vpiHandle> kLocals = ObjectsOf(vpiVariables, s);
  ASSERT_EQ(kLocals.size(), 1U);
  EXPECT_EQ(vpi_get(vpiType, kLocals[0]), vpiStructVar);
  EXPECT_EQ(OrderedNamesOf(vpiMember, kLocals[0]),
            (std::vector<std::string>{"f", "g"}));
  EXPECT_EQ(KindsOf(vpiMember, kLocals[0]),
            (std::vector<int>{vpiLogicVar, vpiIntVar}));
  const std::vector<vpiHandle> kParts = OperandsOf(vpi_handle(vpiExpr, s));
  ASSERT_GE(kParts.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kParts[1]), vpiIntVar);
  EXPECT_STREQ(vpi_get_str(vpiFullName, kParts[1]), "top.s.p.g");
  EXPECT_NE(vpi_compare_objects(vpi_handle(vpiParent, kParts[1]), kLocals[0]),
            0);
}

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
