#include <gtest/gtest.h>

#include <cstring>
#include <string>
#include <vector>

#include "helpers_vpi_put_array_run.h"
#include "helpers_vpi_put_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct TargetPutResults {
  std::vector<PLI_INT32> errors;
  std::vector<int> read_at_once;
};

TargetPutResults results;

vpiHandle MemberNamed(vpiHandle parent, PLI_INT32 relation, const char* name) {
  vpiHandle it = vpi_iterate(relation, parent);
  for (vpiHandle v = it != nullptr ? vpi_scan(it) : nullptr; v != nullptr;
       v = vpi_scan(it)) {
    if (std::strcmp(vpi_get_str(vpiName, v), name) == 0) {
      vpi_release_handle(it);
      return v;
    }
  }
  return nullptr;
}

class ArrayTargetsOfARun : public ArrayPutsOfARun {
 protected:
  void SetUp() override {
    ArrayPutsOfARun::SetUp();
    results = {};
  }

  static void ExpectRefusedAndKept(const char* array) {
    EXPECT_EQ(PutInts(array, {0}, {7, 8}), vpiError) << array;
    vpiHandle handle = HandleNamed(array);
    EXPECT_EQ(IntAt(handle, 0), 3) << array;
    EXPECT_EQ(IntAt(handle, 1), 4) << array;
  }

  static void ExpectWritten(const char* array, const char* first,
                            const char* second) {
    EXPECT_EQ(PutInts(array, {0}, {7, 8}), 0) << array;
    EXPECT_EQ(IntsNamed({first, second}), (std::vector<int>{7, 8})) << array;
  }
};

TEST_F(ArrayTargetsOfARun, DISABLED_ANetArrayTakesTheValuesOnItsNets) {
  Run("module top; wire [7:0] w [4]; initial $noop; endmodule\n");
  EXPECT_EQ(PutInts("top.w", {0}, {1, 2, 3, 4}), 0);
  EXPECT_EQ(IntsNamed({"top.w[0]", "top.w[1]", "top.w[2]", "top.w[3]"}),
            (std::vector<int>{1, 2, 3, 4}));
}

TEST_F(ArrayTargetsOfARun, ADynamicAssociativeOrQueueArrayIsRefused) {
  Run("module top; int d [], q [$], aa [int];\n"
      "  initial begin d = '{3, 4}; q = '{3, 4}; aa[0] = 3; aa[1] = 4; end\n"
      "endmodule\n");
  ExpectRefusedAndKept("top.d");
  ExpectRefusedAndKept("top.q");
  ExpectRefusedAndKept("top.aa");
}

TEST_F(ArrayTargetsOfARun, AnArrayOfStringsOrOfDynamicElementsIsRefused) {
  Putter() = [] {
    for (const char* name : {"top.da", "top.dq", "top.ds"}) {
      results.errors.push_back(PutInts(name, {0}, {7, 8}));
    }
  };
  Run("module top; string s [2] = '{\"a\", \"b\"};\n"
      "  int da [2][], dq [2][$], ds [2][string], kept [2];\n"
      "  initial begin da[0] = '{3}; dq[0] = '{4}; ds[0][\"k\"] = 5; $put;\n"
      "    kept = '{da[0][0], dq[0][0]}; end\n"
      "endmodule\n");
  EXPECT_EQ(results.errors,
            (std::vector<PLI_INT32>{vpiError, vpiError, vpiError}));
  EXPECT_EQ(IntsNamed({"top.kept[0]", "top.kept[1]"}),
            (std::vector<int>{3, 4}));
  EXPECT_EQ(PutInts("top.s", {0}, {7, 8}), vpiError);
  s_vpi_value text = {};
  text.format = vpiStringVal;
  vpi_get_value(HandleNamed("top.s[0]"), &text);
  EXPECT_STREQ(text.value.str, "a");
}

TEST_F(ArrayTargetsOfARun, AnAutomaticArrayIsRefusedBesideAStaticOne) {
  Putter() = [] {
    vpiHandle frame = vpi_handle(vpiFrame, nullptr);
    vpiHandle local = MemberNamed(frame, vpiAutomatics, "la");
    results.errors.push_back(local == nullptr ? -1
                                              : PutIntsAt(local, {0}, {7, 8}));
    results.errors.push_back(PutInts("top.sa", {0}, {7, 8}));
  };
  Run("module top; int sa [2], seen [2];\n"
      "  task automatic t; int la [2] = '{3, 4}; $put; seen = la; endtask\n"
      "  initial t;\n"
      "endmodule\n");
  EXPECT_EQ(results.errors, (std::vector<PLI_INT32>{vpiError, 0}));
  EXPECT_EQ(IntsNamed({"top.seen[0]", "top.seen[1]"}),
            (std::vector<int>{3, 4}));
  EXPECT_EQ(IntsNamed({"top.sa[0]", "top.sa[1]"}), (std::vector<int>{7, 8}));
}

TEST_F(ArrayTargetsOfARun,
       DISABLED_AnInstanceClassPropertyIsRefusedBesideAStaticOne) {
  Putter() = [] {
    vpiHandle object = vpi_handle(vpiClassObj, HandleNamed("top.c"));
    for (const char* name : {"a", "s"}) {
      vpiHandle property = MemberNamed(object, vpiVariables, name);
      results.errors.push_back(
          property == nullptr ? -1 : PutIntsAt(property, {0}, {7, 8}));
    }
  };
  Run("module top;\n"
      "  class C; int a [2] = '{3, 4}; static int s [2]; endclass\n"
      "  C c = new; int kept [2];\n"
      "  initial begin $put; kept = '{c.a[0], C::s[1]}; end\n"
      "endmodule\n");
  EXPECT_EQ(results.errors, (std::vector<PLI_INT32>{vpiError, 0}));
  EXPECT_EQ(IntsNamed({"top.kept[0]", "top.kept[1]"}),
            (std::vector<int>{3, 8}));
}

TEST_F(ArrayTargetsOfARun, DISABLED_AnArrayOfAnUnpackedStructOrUnionIsRefused) {
  Run("module top;\n"
      "  typedef struct { int a; byte b; } s_t;\n"
      "  typedef union { int a; shortint b; } u_t;\n"
      "  s_t sa [4]; u_t ua [4];\n"
      "  initial begin sa[0].a = 3; ua[0].a = 3; end\n"
      "endmodule\n");
  EXPECT_EQ(PutInts("top.sa", {0}, {7, 8}), vpiError);
  EXPECT_EQ(PutInts("top.ua", {0}, {7, 8}), vpiError);
  EXPECT_EQ(IntNamed("top.sa[0].a"), 3);
  EXPECT_EQ(IntNamed("top.ua[0].a"), 3);
}

TEST_F(ArrayTargetsOfARun, AnArrayOfAPackedStructIsWritten) {
  Run("module top;\n"
      "  typedef struct packed { byte a; byte b; } p_t;\n"
      "  p_t pa [4]; initial $noop;\n"
      "endmodule\n");
  ExpectWritten("top.pa", "top.pa[0]", "top.pa[1]");
}

TEST_F(ArrayTargetsOfARun, DISABLED_AStaticArrayOfAPackageIsWritten) {
  Run("package p; int a [2]; endpackage\n"
      "module top; initial $noop; endmodule\n");
  ExpectWritten("p::a", "p::a[0]", "p::a[1]");
}

TEST_F(ArrayTargetsOfARun, DISABLED_AStaticArrayOfTheCompilationUnitIsWritten) {
  Run("int u [2];\n"
      "module top; initial $noop; endmodule\n");
  ExpectWritten("$unit::u", "$unit::u[0]", "$unit::u[1]");
}

TEST_F(ArrayTargetsOfARun, AStaticArrayOfAnInterfaceOrProgramIsWritten) {
  Run("interface ifc; int a [2]; endinterface\n"
      "program prg; int a [2]; endprogram\n"
      "module top; ifc i(); prg pg(); initial $noop; endmodule\n");
  ExpectWritten("top.i.a", "top.i.a[0]", "top.i.a[1]");
  ExpectWritten("top.pg.a", "top.pg.a[0]", "top.pg.a[1]");
}

TEST_F(ArrayTargetsOfARun, DISABLED_AStaticArrayOfANamedBlockIsWritten) {
  Run("module top; initial begin : blk int a [2]; end endmodule\n");
  ExpectWritten("top.blk.a", "top.blk.a[0]", "top.blk.a[1]");
}

TEST_F(ArrayTargetsOfARun, EveryFormatButItsNineIsRefused) {
  Run("module top; logic [7:0] a [2] = '{3, 4}; initial $noop; endmodule\n");
  char text[] = "7";
  for (const PLI_INT32 kFormat :
       {vpiOctStrVal, vpiDecStrVal, vpiHexStrVal, vpiScalarVal, vpiStrengthVal,
        vpiStringVal, vpiObjTypeVal, vpiSuppressVal}) {
    s_vpi_arrayvalue value = {};
    value.format = kFormat;
    value.value.rawvals = text;
    EXPECT_EQ(PutArrayAt(HandleNamed("top.a"), value, {0}, 2), vpiError)
        << kFormat;
  }
  EXPECT_EQ(IntsNamed({"top.a[0]", "top.a[1]"}), (std::vector<int>{3, 4}));
}

TEST_F(ArrayTargetsOfARun, DISABLED_AnExplicitNoDelayIsAcceptedWithEitherFlag) {
  Run("module top; int a [2], b [2], c [2], d [2]; initial $noop;\n"
      "endmodule\n");
  EXPECT_EQ(PutInts("top.a", {0}, {7, 8}, vpiNoDelay), 0);
  EXPECT_EQ(PutOneInt("top.b", 5, 2, vpiNoDelay), 0);
  EXPECT_EQ(PutInts("top.c", {0}, {3, 4}, vpiNoDelay | vpiPropagateOff), 0);
  EXPECT_EQ(PutOneInt("top.d", 6, 2, vpiNoDelay | vpiPropagateOff), 0);
  EXPECT_EQ(IntsNamed({"top.a[0]", "top.a[1]", "top.b[0]", "top.b[1]",
                       "top.c[0]", "top.c[1]", "top.d[0]", "top.d[1]"}),
            (std::vector<int>{7, 8, 5, 5, 3, 4, 6, 6}));
}

TEST_F(ArrayTargetsOfARun, EveryDelayOrEventModeIsRefused) {
  Run("module top; int a [2] = '{3, 4}; initial $noop; endmodule\n");
  for (const PLI_UINT32 kMode :
       {vpiInertialDelay, vpiTransportDelay, vpiPureTransportDelay,
        vpiForceFlag, vpiReleaseFlag, vpiCancelEvent, vpiReturnEvent}) {
    EXPECT_EQ(PutInts("top.a", {0}, {7, 8}, kMode), vpiError) << kMode;
  }
  EXPECT_EQ(IntsNamed({"top.a[0]", "top.a[1]"}), (std::vector<int>{3, 4}));
}

TEST_F(ArrayTargetsOfARun, ShortIntsLandInAShortintOrLongintArray) {
  Run("module top; shortint s [2]; longint l [2]; initial $noop;\n"
      "endmodule\n");
  PLI_INT16 shorts[2] = {300, -5};
  s_vpi_arrayvalue value = {};
  value.format = vpiShortIntVal;
  value.value.shortints = shorts;
  EXPECT_EQ(PutArrayAt(HandleNamed("top.s"), value, {0}, 2), 0);
  EXPECT_EQ(PutArrayAt(HandleNamed("top.l"), value, {0}, 2), 0);
  EXPECT_EQ(IntsNamed({"top.s[0]", "top.s[1]", "top.l[0]"}),
            (std::vector<int>{300, -5, 300}));
  EXPECT_EQ(BitsNamed("top.l[1]"), std::string(61, '1') + "011");
}

TEST_F(ArrayTargetsOfARun, LongIntsLandInALongintArrayWithAllSixtyFourBits) {
  Run("module top; longint l [2]; initial $noop; endmodule\n");
  PLI_INT64 longs[2] = {-3, static_cast<PLI_INT64>(0x8000000000000001ULL)};
  s_vpi_arrayvalue value = {};
  value.format = vpiLongIntVal;
  value.value.longints = longs;
  EXPECT_EQ(PutArrayAt(HandleNamed("top.l"), value, {0}, 2), 0);
  EXPECT_EQ(BitsNamed("top.l[0]"), std::string(62, '1') + "01");
  EXPECT_EQ(BitsNamed("top.l[1]"), "1" + std::string(62, '0') + "1");
}

}  // namespace
}  // namespace delta
