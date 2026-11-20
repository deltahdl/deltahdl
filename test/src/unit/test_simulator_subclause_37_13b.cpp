#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class IoDeclItemsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle Io(vpiHandle owner, const char* name) {
    return Named(vpiIODecl, owner, name);
  }

  static vpiHandle Tf(vpiHandle scope, const char* name) {
    return Named(vpiTaskFunc, scope, name);
  }

  static vpiHandle Method(const char* cls, const char* name) {
    return Tf(Named(vpiClassDefn, By("top"), cls), name);
  }

  static vpiHandle ModportIo(const char* inst, const char* modport,
                             const char* name) {
    return Io(Named(vpiModport, By(inst), modport), name);
  }

  static bool Same(vpiHandle a, vpiHandle b) {
    return a != nullptr && VpiObjectOf(a) == VpiObjectOf(b);
  }

  static int KindOf(vpiHandle obj) {
    return obj == nullptr ? 0 : vpi_get(vpiType, obj);
  }

  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }

  static std::string NameOf(vpiHandle obj) {
    const char* text = obj == nullptr ? nullptr : vpi_get_str(vpiName, obj);
    return text == nullptr ? "" : text;
  }

  static void ExpectShape(vpiHandle io, int size, int is_signed, int scalar,
                          int vector) {
    ASSERT_NE(io, nullptr);
    std::string at = NameOf(io);
    EXPECT_EQ(vpi_get(vpiSize, io), size) << at;
    EXPECT_EQ(vpi_get(vpiSigned, io), is_signed) << at;
    EXPECT_EQ(vpi_get(vpiScalar, io), scalar) << at;
    EXPECT_EQ(vpi_get(vpiVector, io), vector) << at;
  }

  static void ExpectBound(vpiHandle io_bound, vpiHandle ts_bound,
                          const std::string& at) {
    ASSERT_EQ(io_bound == nullptr, ts_bound == nullptr) << at;
    if (io_bound != nullptr) EXPECT_EQ(IntOf(io_bound), IntOf(ts_bound)) << at;
  }

  static void ExpectRangesOfItsTypespec(vpiHandle io) {
    ASSERT_NE(io, nullptr);
    std::string at = NameOf(io);
    vpiHandle ts = vpi_handle(vpiTypespec, io);
    ASSERT_NE(ts, nullptr) << at;
    std::vector<vpiHandle> io_ranges = ObjectsOf(vpiRange, io);
    std::vector<vpiHandle> ts_ranges = ObjectsOf(vpiRange, ts);
    ASSERT_EQ(io_ranges.size(), ts_ranges.size()) << at;
    for (std::size_t i = 0; i < io_ranges.size(); ++i) {
      ExpectBound(vpi_handle(vpiLeftRange, io_ranges[i]),
                  vpi_handle(vpiLeftRange, ts_ranges[i]), at);
      ExpectBound(vpi_handle(vpiRightRange, io_ranges[i]),
                  vpi_handle(vpiRightRange, ts_ranges[i]), at);
    }
    ExpectBound(vpi_handle(vpiLeftRange, io), vpi_handle(vpiLeftRange, ts), at);
    ExpectBound(vpi_handle(vpiRightRange, io), vpi_handle(vpiRightRange, ts),
                at);
  }

  static void ExpectRefObjOver(vpiHandle io, int actual_kind) {
    ASSERT_NE(io, nullptr);
    vpiHandle expr = vpi_handle(vpiExpr, io);
    EXPECT_EQ(KindOf(expr), vpiRefObj) << NameOf(io);
    EXPECT_EQ(KindOf(vpi_handle(vpiActual, expr)), actual_kind) << NameOf(io);
  }
};

using Names = std::vector<std::string>;

constexpr const char* kModulePorts =
    "module sub(input logic signed [3:0] d, input logic e,\n"
    "           output logic [1:0][3:0] p, input logic u [2]);\n"
    "endmodule\n"
    "module top; logic signed [3:0] d; logic e; logic [1:0][3:0] p;\n"
    "  logic u [2]; sub s(.d(d), .e(e), .p(p), .u(u));\n"
    "endmodule\n";

TEST_F(IoDeclItemsOfARun, DISABLED_AModulePortsIoDeclDescribesItsPort) {
  Run(kModulePorts);
  ExpectShape(Io(By("top.s"), "d"), 4, 1, 0, 1);
  ExpectShape(Io(By("top.s"), "e"), 1, 0, 1, 0);
}

TEST_F(IoDeclItemsOfARun, DISABLED_AModulePortsRangesAreItsTypespecs) {
  Run(kModulePorts);
  vpiHandle p = Io(By("top.s"), "p");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(ObjectsOf(vpiRange, p).size(), 2U);
  EXPECT_EQ(IntOf(vpi_handle(vpiLeftRange, p)), 1);
  EXPECT_EQ(IntOf(vpi_handle(vpiRightRange, p)), 0);
  for (const char* name : {"d", "e", "p", "u"}) {
    ExpectRangesOfItsTypespec(Io(By("top.s"), name));
  }
}

TEST_F(IoDeclItemsOfARun, DISABLED_AModulePortsIoDeclReachesItsTypespec) {
  Run(kModulePorts);
  vpiHandle ts = vpi_handle(vpiTypespec, Io(By("top.s"), "d"));
  ASSERT_NE(ts, nullptr);
  EXPECT_EQ(KindOf(ts), vpiLogicTypespec);
  EXPECT_EQ(vpi_get(vpiSigned, ts), 1);
  EXPECT_EQ(IntOf(vpi_handle(vpiLeftRange, ts)), 3);
  EXPECT_EQ(IntOf(vpi_handle(vpiRightRange, ts)), 0);
}

TEST_F(IoDeclItemsOfARun, AModulePortsIoDeclReachesItsModule) {
  Run(kModulePorts);
  EXPECT_TRUE(Same(vpi_handle(vpiModule, Io(By("top.s"), "d")), By("top.s")));
}

constexpr const char* kSubroutineArgs =
    "  typedef logic [3:0] nib_t;\n"
    "  function automatic void f(input logic signed [7:0] a, input logic b,\n"
    "      input nib_t n, ref int r, const ref int cr); endfunction\n"
    "  task automatic t(input logic signed [7:0] a, input logic b,\n"
    "      input nib_t n, ref int r, const ref int cr); endtask\n";

std::string ArgsDesign() {
  return std::string("module top;\n") + kSubroutineArgs + "  class C;\n" +
         kSubroutineArgs + "  endclass\nendmodule\n";
}

TEST_F(IoDeclItemsOfARun, FunctionAndMethodArgumentsDescribeThemselves) {
  Run(ArgsDesign());
  for (vpiHandle tf :
       {Tf(By("top"), "f"), Method("C", "f"), Method("C", "t")}) {
    ASSERT_NE(tf, nullptr);
    ExpectShape(Io(tf, "a"), 8, 1, 0, 1);
    ExpectShape(Io(tf, "b"), 1, 0, 1, 0);
  }
}

TEST_F(IoDeclItemsOfARun,
       DISABLED_FunctionAndMethodArgumentsReachTheirTypespecs) {
  Run(ArgsDesign());
  for (vpiHandle tf :
       {Tf(By("top"), "f"), Method("C", "f"), Method("C", "t")}) {
    ASSERT_NE(tf, nullptr);
    vpiHandle a = Io(tf, "a");
    ASSERT_NE(a, nullptr);
    vpiHandle ts = vpi_handle(vpiTypespec, a);
    EXPECT_EQ(KindOf(ts), vpiLogicTypespec) << NameOf(tf);
    if (ts != nullptr) {
      EXPECT_EQ(IntOf(vpi_handle(vpiLeftRange, ts)), 7) << NameOf(tf);
      EXPECT_EQ(IntOf(vpi_handle(vpiRightRange, ts)), 0) << NameOf(tf);
    }
    vpiHandle n = Io(tf, "n");
    ASSERT_NE(n, nullptr);
    EXPECT_EQ(NameOf(vpi_handle(vpiTypespec, n)), "nib_t") << NameOf(tf);
  }
  EXPECT_EQ(NameOf(vpi_handle(vpiTypespec, Io(Tf(By("top"), "t"), "n"))),
            "nib_t");
}

TEST_F(IoDeclItemsOfARun, FunctionAndMethodRefArgumentsAreVpiRef) {
  Run(ArgsDesign());
  for (vpiHandle tf :
       {Tf(By("top"), "f"), Method("C", "f"), Method("C", "t")}) {
    ASSERT_NE(tf, nullptr);
    EXPECT_EQ(vpi_get(vpiDirection, Io(tf, "r")), vpiRef) << NameOf(tf);
    EXPECT_EQ(vpi_get(vpiDirection, Io(tf, "a")), vpiInput) << NameOf(tf);
  }
}

TEST_F(IoDeclItemsOfARun, AConstRefArgumentIsVpiRef) {
  Run(ArgsDesign());
  for (vpiHandle tf : {Tf(By("top"), "f"), Tf(By("top"), "t"), Method("C", "f"),
                       Method("C", "t")}) {
    ASSERT_NE(tf, nullptr);
    EXPECT_EQ(vpi_get(vpiDirection, Io(tf, "cr")), vpiRef) << NameOf(tf);
  }
}

TEST_F(IoDeclItemsOfARun, FunctionAndMethodRefArgumentsReachRefObjs) {
  Run(ArgsDesign());
  for (vpiHandle tf :
       {Tf(By("top"), "f"), Method("C", "f"), Method("C", "t")}) {
    ASSERT_NE(tf, nullptr);
    ExpectRefObjOver(Io(tf, "r"), vpiIntVar);
    ExpectRefObjOver(Io(tf, "cr"), vpiIntVar);
  }
}

TEST_F(IoDeclItemsOfARun, DISABLED_AnArgumentsIoDeclReachesItsTaskOrFunction) {
  Run(ArgsDesign());
  for (vpiHandle tf : {Tf(By("top"), "f"), Tf(By("top"), "t"), Method("C", "f"),
                       Method("C", "t")}) {
    ASSERT_NE(tf, nullptr);
    vpiHandle a = Io(tf, "a");
    bool is_task = KindOf(tf) == vpiTask;
    EXPECT_TRUE(Same(vpi_handle(vpiTaskFunc, a), tf)) << NameOf(tf);
    EXPECT_EQ(Same(vpi_handle(vpiTask, a), tf), is_task) << NameOf(tf);
    EXPECT_EQ(Same(vpi_handle(vpiFunction, a), tf), !is_task) << NameOf(tf);
    EXPECT_EQ(vpi_handle(is_task ? vpiFunction : vpiTask, a), nullptr)
        << NameOf(tf);
  }
}

constexpr const char* kArrayArgs =
    "module top;\n"
    "  task automatic t(input int c[2], input logic [1:0][3:0] m,\n"
    "      input int dy[], input int q[$], input int as[string],\n"
    "      input logic b);\n"
    "  endtask\n"
    "endmodule\n";

TEST_F(IoDeclItemsOfARun, DISABLED_AnUnpackedArgumentsRangesAreItsTypespecs) {
  Run(kArrayArgs);
  vpiHandle c = Io(Tf(By("top"), "t"), "c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(ObjectsOf(vpiRange, c).size(), 1U);
  ExpectRangesOfItsTypespec(c);
}

TEST_F(IoDeclItemsOfARun, DISABLED_APackedArgumentHasARangePerDimension) {
  Run(kArrayArgs);
  vpiHandle m = Io(Tf(By("top"), "t"), "m");
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(ObjectsOf(vpiRange, m).size(), 2U);
  EXPECT_EQ(IntOf(vpi_handle(vpiLeftRange, m)), 1);
  EXPECT_EQ(IntOf(vpi_handle(vpiRightRange, m)), 0);
  ExpectRangesOfItsTypespec(m);
}

TEST_F(IoDeclItemsOfARun, DISABLED_AVariableSizedArgumentHasNoBounds) {
  Run(kArrayArgs);
  for (const char* name : {"dy", "q", "as"}) {
    vpiHandle io = Io(Tf(By("top"), "t"), name);
    ASSERT_NE(io, nullptr) << name;
    EXPECT_EQ(vpi_handle(vpiLeftRange, io), nullptr) << name;
    EXPECT_EQ(vpi_handle(vpiRightRange, io), nullptr) << name;
    ExpectRangesOfItsTypespec(io);
  }
}

TEST_F(IoDeclItemsOfARun, AScalarArgumentHasNoRanges) {
  Run(kArrayArgs);
  vpiHandle b = Io(Tf(By("top"), "t"), "b");
  ASSERT_NE(b, nullptr);
  EXPECT_TRUE(ObjectsOf(vpiRange, b).empty());
  EXPECT_EQ(vpi_handle(vpiLeftRange, b), nullptr);
  EXPECT_EQ(vpi_handle(vpiRightRange, b), nullptr);
}

constexpr const char* kModportSignals =
    "interface ifc; logic signed [5:0] s; logic t; logic [3:0] w [2];\n"
    "  modport mp(input s, output t, input w);\n"
    "endinterface\n"
    "module top; ifc i0(); endmodule\n";

TEST_F(IoDeclItemsOfARun, AModportIoDeclDescribesTheSignalItNames) {
  Run(kModportSignals);
  ExpectShape(ModportIo("top.i0", "mp", "s"), 6, 1, 0, 1);
  ExpectShape(ModportIo("top.i0", "mp", "t"), 1, 0, 1, 0);
}

TEST_F(IoDeclItemsOfARun, AModportIoDeclsRangesAreItsTypespecs) {
  Run(kModportSignals);
  vpiHandle s = ModportIo("top.i0", "mp", "s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(IntOf(vpi_handle(vpiLeftRange, s)), 5);
  EXPECT_EQ(IntOf(vpi_handle(vpiRightRange, s)), 0);
  for (const char* name : {"s", "t", "w"}) {
    ExpectRangesOfItsTypespec(ModportIo("top.i0", "mp", name));
  }
}

TEST_F(IoDeclItemsOfARun, DISABLED_AModportIoDeclReachesItsTypespec) {
  Run(kModportSignals);
  vpiHandle s = ModportIo("top.i0", "mp", "s");
  ASSERT_NE(s, nullptr);
  vpiHandle ts = vpi_handle(vpiTypespec, s);
  ASSERT_NE(ts, nullptr);
  EXPECT_EQ(KindOf(ts), vpiLogicTypespec);
  EXPECT_EQ(vpi_get(vpiSigned, ts), 1);
  EXPECT_EQ(IntOf(vpi_handle(vpiLeftRange, ts)), 5);
}

constexpr const char* kInterfacePorts =
    "interface ifc; logic a; modport mp(input a); endinterface\n"
    "module gen(interface g); endmodule\n"
    "module viamp(ifc.mp m); endmodule\n"
    "module top; ifc i0(); gen u(i0); viamp v(i0.mp); endmodule\n";

TEST_F(IoDeclItemsOfARun, AGenericInterfacePortReachesARefObj) {
  Run(kInterfacePorts);
  vpiHandle g = Io(By("top.u"), "g");
  ASSERT_NE(g, nullptr);
  vpiHandle expr = vpi_handle(vpiExpr, g);
  EXPECT_EQ(KindOf(expr), vpiRefObj);
  EXPECT_TRUE(Same(vpi_handle(vpiActual, expr), By("top.i0")));
}

TEST_F(IoDeclItemsOfARun, AModportPortReachesARefObj) {
  Run(kInterfacePorts);
  vpiHandle m = Io(By("top.v"), "m");
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(KindOf(vpi_handle(vpiExpr, m)), vpiRefObj);
}

TEST_F(IoDeclItemsOfARun, InterfaceAndModportPortsHaveNoDirection) {
  Run(kInterfacePorts);
  EXPECT_EQ(vpi_get(vpiDirection, Io(By("top.u"), "g")), vpiNoDirection);
  EXPECT_EQ(vpi_get(vpiDirection, Io(By("top.v"), "m")), vpiNoDirection);
}

constexpr const char* kVirtualArgs =
    "interface inner; endinterface\n"
    "module top; inner n();\n"
    "  task t(virtual inner w); endtask\n"
    "  function void f(virtual inner w); endfunction\n"
    "endmodule\n";

TEST_F(IoDeclItemsOfARun, AVirtualInterfaceArgumentReachesItsVar) {
  Run(kVirtualArgs);
  for (const char* tf : {"t", "f"}) {
    vpiHandle w = Io(Tf(By("top"), tf), "w");
    ASSERT_NE(w, nullptr) << tf;
    EXPECT_EQ(KindOf(vpi_handle(vpiExpr, w)), vpiVirtualInterfaceVar) << tf;
  }
}

TEST_F(IoDeclItemsOfARun, AVirtualInterfaceFunctionArgumentHasNoDirection) {
  Run(kVirtualArgs);
  EXPECT_EQ(vpi_get(vpiDirection, Io(Tf(By("top"), "f"), "w")), vpiNoDirection);
}

constexpr const char* kInstancePorts =
    "interface bus(input logic clk, output logic o); endinterface\n"
    "program prg(input logic clk, inout wire io); endprogram\n"
    "module sub(input logic clk); endmodule\n"
    "module top; logic clk, o; wire io;\n"
    "  bus b(clk, o); prg p(clk, io); sub s(clk);\n"
    "endmodule\n";

TEST_F(IoDeclItemsOfARun, AnInterfaceIteratesAnIoDeclPerPort) {
  Run(kInstancePorts);
  vpiHandle b = By("top.b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(NamesOf(vpiIODecl, b), (Names{"clk", "o"}));
  EXPECT_EQ(vpi_get(vpiDirection, Io(b, "clk")), vpiInput);
  EXPECT_EQ(vpi_get(vpiDirection, Io(b, "o")), vpiOutput);
}

TEST_F(IoDeclItemsOfARun, AProgramIteratesAnIoDeclPerPort) {
  Run(kInstancePorts);
  vpiHandle p = By("top.p");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(NamesOf(vpiIODecl, p), (Names{"clk", "io"}));
  EXPECT_EQ(vpi_get(vpiDirection, Io(p, "clk")), vpiInput);
  EXPECT_EQ(vpi_get(vpiDirection, Io(p, "io")), vpiInout);
}

TEST_F(IoDeclItemsOfARun, EveryInstanceKindsIoDeclReachesItsInstance) {
  Run(kInstancePorts);
  for (const char* inst : {"top.b", "top.p", "top.s"}) {
    EXPECT_TRUE(Same(vpi_handle(vpiInstance, Io(By(inst), "clk")), By(inst)))
        << inst;
  }
}

constexpr const char* kAnsiUdp =
    "primitive my_or(output o, input a, input b);\n"
    "  table\n"
    "    1 ? : 1;\n"
    "    ? 1 : 1;\n"
    "    0 0 : 0;\n"
    "  endtable\n"
    "endprimitive\n"
    "module top; wire o; my_or u1(o, 1'b1, 1'b0); endmodule\n";

TEST_F(IoDeclItemsOfARun, AnAnsiUdpDefnIteratesAnIoDeclPerPort) {
  Run(kAnsiUdp);
  std::vector<vpiHandle> prims = ObjectsOf(vpiPrimitive, By("top"));
  ASSERT_EQ(prims.size(), 1U);
  vpiHandle defn = vpi_handle(vpiUdpDefn, prims[0]);
  ASSERT_NE(defn, nullptr);
  EXPECT_EQ(NamesOf(vpiIODecl, defn), (Names{"a", "b", "o"}));
  EXPECT_EQ(vpi_get(vpiDirection, Io(defn, "o")), vpiOutput);
  EXPECT_EQ(vpi_get(vpiDirection, Io(defn, "a")), vpiInput);
  EXPECT_EQ(vpi_get(vpiDirection, Io(defn, "b")), vpiInput);
}

TEST_F(IoDeclItemsOfARun, AUdpIoDeclReachesItsDefn) {
  Run(kAnsiUdp);
  std::vector<vpiHandle> prims = ObjectsOf(vpiPrimitive, By("top"));
  ASSERT_EQ(prims.size(), 1U);
  vpiHandle defn = vpi_handle(vpiUdpDefn, prims[0]);
  ASSERT_NE(defn, nullptr);
  for (vpiHandle io : ObjectsOf(vpiIODecl, defn)) {
    EXPECT_TRUE(Same(vpi_handle(vpiUdpDefn, io), defn)) << NameOf(io);
  }
}

}  // namespace
}  // namespace delta
