#include <gtest/gtest.h>

#include <cstring>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

namespace {

DpiArg StringFormal(Direction direction) {
  DpiArg formal;
  formal.name = "s";
  formal.type = DataTypeKind::kString;
  formal.direction = direction;
  return formal;
}

TEST(DpiStringMembers, AStringMemberOfAnAggregateIsAConstCharPointer) {
  EXPECT_EQ(DpiCTypeOfStringMember(), "const char*");
  EXPECT_EQ(DpiCTypeOfStringMember(),
            DpiCTypeOfBasicType(DataTypeKind::kString, false));
  DpiAggregateElement record;
  record.kind = DataTypeKind::kStruct;
  record.members = {DpiAggregateElement{DataTypeKind::kString, 0, {}},
                    DpiAggregateElement{DataTypeKind::kInt, 0, {}}};
  EXPECT_TRUE(DpiAggregateIsAnArgument(record));
}

TEST(DpiStringMembers, AStringMemberFollowsTheStandaloneStipulations) {
  EXPECT_TRUE(DpiStringMemberStipulationsAreStandalone());
  EXPECT_EQ(
      DpiSideProvidingStringPointer(DpiStringPointerProvider::kImportInput),
      DpiMemorySide::kSystemVerilog);
  EXPECT_EQ(DpiSideCopyingString(DpiStringPointerProvider::kImportInoutChanged),
            DpiMemorySide::kSystemVerilog);
  EXPECT_FALSE(DpiStringCharactersMayBeModifiedByReceiver());
}

TEST(DpiStringMembers, AnArrayOfStringsIsConstCharPointerPointerRegardless) {
  for (const Direction kDirection :
       {Direction::kInput, Direction::kOutput, Direction::kInout}) {
    EXPECT_EQ(DpiCTypeOfStringArray(kDirection), "const char**");
  }
  EXPECT_NE(DpiCTypeOfStringArray(Direction::kInput),
            DpiCTypeOfFormal(StringFormal(Direction::kInput), false));
  EXPECT_EQ(DpiCTypeOfStringArray(Direction::kOutput),
            DpiCTypeOfFormal(StringFormal(Direction::kOutput), false));
  EXPECT_EQ(DpiCTypeOfStringArray(Direction::kInout),
            DpiCTypeOfFormal(StringFormal(Direction::kInout), false));
}

TEST(DpiStringMembers, AnUnpackedArrayOfStringsIsDeclaredTheSameInEveryMode) {
  const std::vector<SvActualDimension> kThree = {{0, 2}};
  for (const Direction kDirection :
       {Direction::kInput, Direction::kOutput, Direction::kInout}) {
    EXPECT_EQ(DpiCDeclarationOfUnpackedFormal(StringFormal(kDirection), kThree),
              "const char* s[3]");
  }
  DpiArg ints = StringFormal(Direction::kInput);
  ints.type = DataTypeKind::kInt;
  EXPECT_EQ(DpiCDeclarationOfUnpackedFormal(ints, kThree), "const int s[3]");
}

struct NamedRecord {
  const char* name;
  int n;
};

long long Matches(const char* s, const char* expected) {
  return s != nullptr && std::strcmp(s, expected) == 0 ? 1 : 0;
}

void GiveNamed(NamedRecord* r) {
  r->name = "given";
  r->n = 5;
}

void ChangeNamed(NamedRecord* r) {
  SeeInC({Matches(r->name, "before"), r->n});
  r->name = "after";
  r->n = 8;
}

TEST(DpiStringMembers, AStringMemberCWritesIsCopiedBack) {
  SimFixture f;
  RunModuleWithC(
      "  typedef struct { string name; int n; } named;\n"
      "  import \"DPI-C\" function void give(output named r);\n"
      "  import \"DPI-C\" function void change(inout named r);\n"
      "  named o, io;\n"
      "  bit ok_o, ok_io;\n"
      "  initial begin\n"
      "    give(o);\n"
      "    io.name = \"before\"; io.n = 3;\n"
      "    change(io);\n"
      "    ok_o = o.name == \"given\" && o.n == 5;\n"
      "    ok_io = io.name == \"after\" && io.n == 8;\n"
      "  end\n",
      f, {{"give", CAddress(&GiveNamed)}, {"change", CAddress(&ChangeNamed)}},
      "annex_h_08_10_01_members");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, 3}));
  EXPECT_EQ(DesignValue(f, "ok_o"), 1U);
  EXPECT_EQ(DesignValue(f, "ok_io"), 1U);
}

void SeeNames(const char** s) {
  SeeInC({Matches(s[0], "ab"), Matches(s[1], ""), Matches(s[2], "cde")});
}

void GiveNames(const char** s) {
  s[0] = "one";
  s[1] = "two";
  s[2] = "three";
}

void ChangeNames(const char** s) {
  SeeNames(s);
  s[1] = "filled";
}

void RunNames(const std::string& body, SimFixture& f) {
  RunModuleWithC(
      "  import \"DPI-C\" function void see(input string s[3]);\n"
      "  import \"DPI-C\" function void give(output string s[3]);\n"
      "  import \"DPI-C\" function void change(inout string s[3]);\n"
      "  string a[3] = '{\"ab\", \"\", \"cde\"};\n"
      "  bit ok;\n"
      "  initial begin\n" +
          body + "  end\n",
      f,
      {{"see", CAddress(&SeeNames)},
       {"give", CAddress(&GiveNames)},
       {"change", CAddress(&ChangeNames)}},
      "annex_h_08_10_01_names");
}

TEST(DpiStringMembers, AnInputArrayOfStringsIsReadByElement) {
  SimFixture f;
  RunNames("    see(a);\n", f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, 1, 1}));
}

TEST(DpiStringMembers, DISABLED_AnOutputArrayOfStringsIsCopiedBack) {
  SimFixture f;
  RunNames(
      "    give(a);\n"
      "    ok = a[0] == \"one\" && a[1] == \"two\" && a[2] == \"three\";\n",
      f);
  EXPECT_EQ(DesignValue(f, "ok"), 1U);
}

TEST(DpiStringMembers, DISABLED_AnInoutArrayOfStringsArrivesAndIsCopiedBack) {
  SimFixture f;
  RunNames(
      "    change(a);\n"
      "    ok = a[0] == \"ab\" && a[1] == \"filled\" && a[2] == \"cde\";\n",
      f);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, 1, 1}));
  EXPECT_EQ(DesignValue(f, "ok"), 1U);
}

void PassNamedRecords() {
  auto take = NamedExport<int (*)(const NamedRecord*)>("take_named");
  auto make = NamedExport<void (*)(NamedRecord*)>("make_named");
  if (take == nullptr || make == nullptr) return;
  const NamedRecord kGiven = {"from C", 6};
  SeeInC({take(&kGiven)});
  NamedRecord made = {"", 0};
  make(&made);
  SeeInC({Matches(made.name, "from SystemVerilog"), made.n});
}

TEST(DpiStringMembers, AnExportTakesAndGivesAStringMember) {
  SimFixture f;
  RunModuleWithC(
      "  typedef struct { string name; int n; } named;\n"
      "  export \"DPI-C\" function take_named;\n"
      "  export \"DPI-C\" function make_named;\n"
      "  import \"DPI-C\" context function void pass_named();\n"
      "  function int take_named(input named r);\n"
      "    return r.name == \"from C\" ? r.n : -1;\n"
      "  endfunction\n"
      "  function void make_named(output named r);\n"
      "    r.name = \"from SystemVerilog\"; r.n = 9;\n"
      "  endfunction\n"
      "  initial pass_named();\n",
      f, {{"pass_named", CAddress(&PassNamedRecords)}},
      "annex_h_08_10_01_exports");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{6, 1, 9}));
}

}  // namespace
