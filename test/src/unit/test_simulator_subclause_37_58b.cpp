#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr const char* kSelects =
    "module top; integer i, j; time t; logic [7:0] r [0:3];\n"
    "  parameter P = 2; parameter [7:0] Q = 8'h5A;\n"
    "  wire w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11;\n"
    "  specify specparam S = 8'h5A; endspecify\n"
    "  assign w1 = i[j];\n"
    "  assign w2 = i[P];\n"
    "  assign w3 = i[P-1];\n"
    "  assign w4 = t[5];\n"
    "  assign w5 = t[j];\n"
    "  assign w6 = Q[3];\n"
    "  assign w7 = Q[j];\n"
    "  assign w8 = S[3];\n"
    "  assign w9 = S[j];\n"
    "  assign w10 = r[i][3];\n"
    "  assign w11 = r[1][3];\n"
    "endmodule\n";

class BitSelectsEverywhere : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run(kSelects);
  }

  static vpiHandle Side(size_t n) {
    const std::vector<vpiHandle> kAssigns = ObjectsOf(vpiContAssign, By("top"));
    return n < kAssigns.size() ? vpi_handle(vpiRhs, kAssigns[n]) : nullptr;
  }

  static std::string Spelling(vpiHandle obj) {
    if (obj == nullptr) return "null";
    if (vpi_get(vpiType, obj) == vpiConstant) {
      return std::to_string(IntegerOf(obj));
    }
    if (vpi_get(vpiType, obj) == vpiOperation) return "op";
    const char* name = vpi_get_str(vpiName, obj);
    return name == nullptr ? "?" : name;
  }

  static void ExpectParent(size_t side, int type, const char* name) {
    vpiHandle select = Side(side);
    ASSERT_NE(select, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiType, select), vpiBitSelect) << name;
    vpiHandle parent = vpi_handle(vpiParent, select);
    ASSERT_NE(parent, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiType, parent), type) << name;
    EXPECT_EQ(Spelling(parent), name) << name;
  }

  static void ExpectIndex(size_t side, const char* index) {
    vpiHandle select = Side(side);
    ASSERT_NE(select, nullptr) << side;
    EXPECT_EQ(Spelling(vpi_handle(vpiIndex, select)), index) << side;
  }

  static void ExpectNames(size_t side, const char* name) {
    vpiHandle select = Side(side);
    ASSERT_NE(select, nullptr) << name;
    EXPECT_EQ(Spelling(select), name);
    const char* full = vpi_get_str(vpiFullName, select);
    EXPECT_EQ(std::string(full == nullptr ? "" : full),
              std::string("top.") + name);
  }
};

TEST_F(BitSelectsEverywhere, ATimeVarsBitSelectsParentIsTheTimeVar) {
  ExpectParent(3, vpiTimeVar, "t");
}

TEST_F(BitSelectsEverywhere, AParametersBitSelectsParentIsTheParameter) {
  ExpectParent(5, vpiParameter, "Q");
}

TEST_F(BitSelectsEverywhere, ASpecParamsBitSelectsParentIsTheSpecParam) {
  ExpectParent(7, vpiSpecParam, "S");
}

TEST_F(BitSelectsEverywhere, AVarSelectsBitSelectsParentIsTheVarSelect) {
  ExpectParent(9, vpiVarSelect, "r[i]");
}

TEST_F(BitSelectsEverywhere, AVariableIndexIsTheVariableWritten) {
  ExpectIndex(0, "j");
}

TEST_F(BitSelectsEverywhere, AParameterIndexIsTheParameterWritten) {
  ExpectIndex(1, "P");
  vpiHandle index = vpi_handle(vpiIndex, Side(1));
  ASSERT_NE(index, nullptr);
  EXPECT_NE(vpi_get(vpiType, index), vpiConstant);
}

TEST_F(BitSelectsEverywhere, AnOperationIndexIsTheOperationWritten) {
  ExpectIndex(2, "op");
  EXPECT_EQ(OpOf(vpi_handle(vpiIndex, Side(2))), vpiSubOp);
}

TEST_F(BitSelectsEverywhere, ATimeVarsBitSelectsIndexIsReached) {
  ExpectIndex(3, "5");
  ExpectIndex(4, "j");
}

TEST_F(BitSelectsEverywhere, AParametersBitSelectsIndexIsReached) {
  ExpectIndex(5, "3");
  ExpectIndex(6, "j");
}

TEST_F(BitSelectsEverywhere, ASpecParamsBitSelectsIndexIsReached) {
  ExpectIndex(7, "3");
  ExpectIndex(8, "j");
}

TEST_F(BitSelectsEverywhere, AVarSelectsBitSelectsIndexIsItsOwn) {
  ExpectIndex(9, "3");
}

TEST_F(BitSelectsEverywhere, ATimeVarsBitSelectIsNamed) {
  ExpectNames(3, "t[5]");
}

TEST_F(BitSelectsEverywhere, AParametersBitSelectIsNamed) {
  ExpectNames(5, "Q[3]");
}

TEST_F(BitSelectsEverywhere, ASpecParamsBitSelectIsNamed) {
  ExpectNames(7, "S[3]");
}

TEST_F(BitSelectsEverywhere, DISABLED_AVarSelectsBitSelectIsNamed) {
  ExpectNames(9, "r[i][3]");
}

TEST_F(BitSelectsEverywhere, AVariablyIndexedBitSelectIsNamed) {
  ExpectNames(0, "i[j]");
}

TEST_F(BitSelectsEverywhere, AVaryingVarSelectParentIsNoConstantSelect) {
  EXPECT_EQ(vpi_get(vpiConstantSelect, Side(9)), 0);
  EXPECT_EQ(vpi_get(vpiConstantSelect, Side(10)), 1);
}

TEST_F(BitSelectsEverywhere, AConstantBitOfEachParentIsAConstantSelect) {
  for (size_t side : {3U, 5U, 7U}) {
    EXPECT_EQ(vpi_get(vpiConstantSelect, Side(side)), 1) << side;
  }
}

class BitSelectsOfSubroutines : public VpiDesignRun {
 protected:
  static vpiHandle LastAssignedIn(vpiHandle routine) {
    vpiHandle last = nullptr;
    for (vpiHandle stmt : ObjectsOf(vpiStmt, vpi_handle(vpiStmt, routine))) {
      if (vpi_get(vpiType, stmt) == vpiAssignment) {
        last = vpi_handle(vpiRhs, stmt);
      }
    }
    return last;
  }
};

TEST_F(BitSelectsOfSubroutines, AnAutomaticVariablesBitIsNoConstantSelect) {
  Run("module top;\n"
      "  function automatic bit fa(); integer a; begin a = 0; fa = a[3]; end\n"
      "  endfunction\n"
      "  function bit fs(); integer s; begin s = 0; fs = s[3]; end\n"
      "  endfunction\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle automatic_bit = LastAssignedIn(Named(vpiFunction, top, "fa"));
  vpiHandle static_bit = LastAssignedIn(Named(vpiFunction, top, "fs"));
  ASSERT_NE(automatic_bit, nullptr);
  ASSERT_NE(static_bit, nullptr);
  EXPECT_EQ(vpi_get(vpiType, automatic_bit), vpiBitSelect);
  EXPECT_EQ(vpi_get(vpiConstantSelect, automatic_bit), 0);
  EXPECT_EQ(vpi_get(vpiConstantSelect, static_bit), 1);
}

}  // namespace
}  // namespace delta
