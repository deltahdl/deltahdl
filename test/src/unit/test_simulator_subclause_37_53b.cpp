#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class SequenceDeclsEverywhere : public VpiDesignRun {
 protected:
  static std::string NameOf(int property, vpiHandle obj) {
    const char* name = obj == nullptr ? nullptr : vpi_get_str(property, obj);
    return name == nullptr ? "" : name;
  }

  static std::vector<std::string> NamesIn(int type, vpiHandle ref) {
    std::vector<std::string> names;
    for (vpiHandle obj : ObjectsOf(type, ref)) {
      names.push_back(NameOf(vpiName, obj));
    }
    return names;
  }

  static vpiHandle ScopeAt(const std::string& path) {
    if (path == "$unit") return Named(vpiPackage, nullptr, "$unit");
    return By(path);
  }

  static void ExpectSequenceAt(const std::string& scope,
                               const char* full_name) {
    vpiHandle decl = Named(vpiSequenceDecl, ScopeAt(scope), "s");
    ASSERT_NE(decl, nullptr) << scope;
    EXPECT_EQ(NameOf(vpiName, decl), "s") << scope;
    EXPECT_EQ(NameOf(vpiFullName, decl), full_name) << scope;
    EXPECT_EQ(NamesIn(vpiSeqFormalDecl, decl), std::vector<std::string>{"v"})
        << scope;
  }

  static vpiHandle FormalOf(const char* sequence, const char* formal) {
    return Named(vpiSeqFormalDecl, Named(vpiSequenceDecl, By("top"), sequence),
                 formal);
  }

  static vpiHandle DeclOfInst(const char* assertion) {
    vpiHandle inst = PropertyOf(assertion);
    if (inst == nullptr || vpi_get(vpiType, inst) != vpiSequenceInst) {
      return nullptr;
    }
    return vpi_handle(vpiSequenceDecl, inst);
  }
};

TEST_F(SequenceDeclsEverywhere, AnInterfacesSequenceReportsItsNames) {
  Run("interface ifc; sequence s(v); v; endsequence endinterface\n"
      "module top; ifc i0(); endmodule\n");
  ExpectSequenceAt("top.i0", "top.i0.s");
}

TEST_F(SequenceDeclsEverywhere, AProgramsSequenceReportsItsNames) {
  Run("program prg; sequence s(v); v; endsequence endprogram\n"
      "module top; prg pr0(); endmodule\n");
  ExpectSequenceAt("top.pr0", "top.pr0.s");
}

TEST_F(SequenceDeclsEverywhere, ACheckersSequenceReportsItsNames) {
  Run("checker chk; sequence s(v); v; endsequence endchecker\n"
      "module top; chk k0(); endmodule\n");
  ExpectSequenceAt("top.k0", "top.k0.s");
}

TEST_F(SequenceDeclsEverywhere,
       DISABLED_ACompilationUnitsSequenceReportsItsNames) {
  Run("sequence s(v); v; endsequence\n"
      "module top; endmodule\n");
  ExpectSequenceAt("$unit", "$unit::s");
}

constexpr const char* kPackageSequences =
    "package pk; logic x;\n"
    "  sequence pf(c, b, a); c ##1 b ##1 a; endsequence\n"
    "  sequence pv; int n; bit f; (x, n = 1, f = 1) ##1 x; endsequence\n"
    "endpackage\n"
    "module top; endmodule\n";

TEST_F(SequenceDeclsEverywhere, APackagesSequenceIteratesFormalsInOrder) {
  Run(kPackageSequences);
  vpiHandle decl = Named(vpiSequenceDecl, By("pk"), "pf");
  ASSERT_NE(decl, nullptr);
  EXPECT_EQ(NamesIn(vpiSeqFormalDecl, decl),
            (std::vector<std::string>{"c", "b", "a"}));
}

TEST_F(SequenceDeclsEverywhere, APackagesSequenceReachesItsLocals) {
  Run(kPackageSequences);
  vpiHandle decl = Named(vpiSequenceDecl, By("pk"), "pv");
  ASSERT_NE(decl, nullptr);
  EXPECT_EQ(NamesIn(vpiVariables, decl), (std::vector<std::string>{"n", "f"}));
  EXPECT_EQ(KindsOf(vpiVariables, decl),
            (std::vector<int>{vpiIntVar, vpiBitVar}));
}

TEST_F(SequenceDeclsEverywhere, OnlyALocalFormalHasADirection) {
  Run("module top; logic a;\n"
      "  sequence s(x, int t, local int n, local output int o);\n"
      "    (a, o = n) ##1 x;\n"
      "  endsequence\n"
      "endmodule\n");
  const struct {
    const char* formal;
    int direction;
  } kFormals[] = {{"x", vpiNoDirection},
                  {"t", vpiNoDirection},
                  {"n", vpiInput},
                  {"o", vpiOutput}};
  for (const auto& formal : kFormals) {
    vpiHandle handle = FormalOf("s", formal.formal);
    ASSERT_NE(handle, nullptr) << formal.formal;
    EXPECT_EQ(vpi_get(vpiDirection, handle), formal.direction) << formal.formal;
  }
}

TEST_F(SequenceDeclsEverywhere,
       DISABLED_ASequenceExpressionDefaultIsReachedAsAnOp) {
  Run("module top; logic a, b;\n"
      "  sequence s(y = a ##1 b); y; endsequence\n"
      "endmodule\n");
  vpiHandle formal = FormalOf("s", "y");
  ASSERT_NE(formal, nullptr);
  vpiHandle value = vpi_handle(vpiExpr, formal);
  ASSERT_NE(value, nullptr);
  EXPECT_EQ(OpOf(value), vpiCycleDelayOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(value);
  ASSERT_GE(kOperands.size(), 2u);
  EXPECT_EQ(NameOf(vpiName, kOperands.front()), "a");
  EXPECT_EQ(NameOf(vpiName, kOperands.back()), "b");
}

TEST_F(SequenceDeclsEverywhere, ANamedEventDefaultIsReachedAsTheEvent) {
  Run("module top; event e;\n"
      "  sequence s(y = e); @(y) 1; endsequence\n"
      "endmodule\n");
  vpiHandle value = vpi_handle(vpiExpr, FormalOf("s", "y"));
  ASSERT_NE(value, nullptr);
  EXPECT_EQ(vpi_get(vpiType, value), vpiNamedEvent);
  EXPECT_EQ(NameOf(vpiName, value), "e");
}

TEST_F(SequenceDeclsEverywhere, AnEventFormalReachesAnEventTypespec) {
  Run("module top; logic a;\n"
      "  sequence s(event e); @(e) a; endsequence\n"
      "endmodule\n");
  vpiHandle formal = FormalOf("s", "e");
  ASSERT_NE(formal, nullptr);
  vpiHandle type = vpi_handle(vpiTypespec, formal);
  ASSERT_NE(type, nullptr);
  EXPECT_EQ(vpi_get(vpiType, type), vpiEventTypespec);
}

TEST_F(SequenceDeclsEverywhere, AnInstInAnotherSequencesBodyReachesItsDecl) {
  Run("module top; logic a, b;\n"
      "  sequence s1; a; endsequence\n"
      "  sequence s2; s1 ##1 b; endsequence\n"
      "endmodule\n");
  vpiHandle body = vpi_handle(vpiExpr, Named(vpiSequenceDecl, By("top"), "s2"));
  const std::vector<vpiHandle> kOperands = OperandsOf(body);
  ASSERT_FALSE(kOperands.empty());
  EXPECT_EQ(vpi_get(vpiType, kOperands.front()), vpiSequenceInst);
  EXPECT_EQ(NameOf(vpiFullName, vpi_handle(vpiSequenceDecl, kOperands.front())),
            "top.s1");
}

TEST_F(SequenceDeclsEverywhere, APackagesSequenceIsReachedHoweverItIsNamed) {
  Run("package pk; logic x;\n"
      "  sequence pq; x; endsequence\n"
      "  sequence ps; x; endsequence\n"
      "  sequence pw; x; endsequence\n"
      "endpackage\n"
      "module top; import pk::*; import pk::ps; logic clk;\n"
      "  k1: assert property (@(posedge clk) pk::pq);\n"
      "  k2: assert property (@(posedge clk) ps);\n"
      "  k3: assert property (@(posedge clk) pw);\n"
      "endmodule\n");
  EXPECT_EQ(NameOf(vpiFullName, DeclOfInst("k1")), "pk::pq");
  EXPECT_EQ(NameOf(vpiFullName, DeclOfInst("k2")), "pk::ps");
  EXPECT_EQ(NameOf(vpiFullName, DeclOfInst("k3")), "pk::pw");
}

TEST_F(SequenceDeclsEverywhere,
       DISABLED_ACompilationUnitsSequenceIsReachedByItsInst) {
  Run("logic ua;\n"
      "sequence us; ua; endsequence\n"
      "module top; logic clk;\n"
      "  k1: assert property (@(posedge clk) us);\n"
      "endmodule\n");
  EXPECT_EQ(NameOf(vpiFullName, DeclOfInst("k1")), "$unit::us");
}

TEST_F(SequenceDeclsEverywhere, AnInterfacesSequenceIsReachedThroughItsInst) {
  Run("interface ifc; logic a; sequence s; a; endsequence endinterface\n"
      "module top; logic clk; ifc u();\n"
      "  k1: assert property (@(posedge clk) u.s);\n"
      "endmodule\n");
  EXPECT_EQ(NameOf(vpiFullName, DeclOfInst("k1")), "top.u.s");
}

}  // namespace
}  // namespace delta
