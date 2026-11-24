#include <gtest/gtest.h>

#include <optional>
#include <string>
#include <string_view>

#include "elaborator/std_package.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(StdPackageContents, TheAnnexListsFiveMembersInOrder) {
  const auto& contents = StdPackageContents();
  ASSERT_EQ(contents.size(), 5u);
  EXPECT_EQ(contents[0].member, StdPackageMember::kSemaphore);
  EXPECT_EQ(contents[0].name, "semaphore");
  EXPECT_EQ(contents[0].kind, StdPackageMemberKind::kClass);
  EXPECT_EQ(contents[1].member, StdPackageMember::kMailbox);
  EXPECT_EQ(contents[1].name, "mailbox");
  EXPECT_EQ(contents[1].kind, StdPackageMemberKind::kClass);
  EXPECT_EQ(contents[2].member, StdPackageMember::kRandomize);
  EXPECT_EQ(contents[2].name, "randomize");
  EXPECT_EQ(contents[2].kind, StdPackageMemberKind::kFunction);
  EXPECT_EQ(contents[3].member, StdPackageMember::kProcess);
  EXPECT_EQ(contents[3].name, "process");
  EXPECT_EQ(contents[3].kind, StdPackageMemberKind::kClass);
  EXPECT_EQ(contents[4].member, StdPackageMember::kWeakReference);
  EXPECT_EQ(contents[4].name, "weak_reference");
  EXPECT_EQ(contents[4].kind, StdPackageMemberKind::kClass);
}

TEST(StdPackageContents, AMemberIsFoundByItsName) {
  for (const StdPackageEntry& entry : StdPackageContents()) {
    EXPECT_EQ(StdPackageMemberName(entry.member), entry.name);
    EXPECT_EQ(KindOfStdPackageMember(entry.member), entry.kind);
    EXPECT_EQ(StdPackageMemberNamed(entry.name), entry.member);
  }
  EXPECT_EQ(StdPackageMemberNamed("queue"), std::nullopt);
  EXPECT_EQ(StdPackageMemberNamed("Semaphore"), std::nullopt);
  EXPECT_EQ(StdPackageMemberNamed(""), std::nullopt);
}

TEST(StdPackageContents, EveryMemberIsProvidedWithoutAUserDefinition) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  semaphore sem;\n"
             "  mailbox mbx;\n"
             "  int v;\n"
             "  int q;\n"
             "  initial begin\n"
             "    static process p = process::self();\n"
             "    weak_reference #(my_obj) wr;\n"
             "    q = std::randomize(v);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(StdPackageContents, ANameOutsideTheListIsNotProvided) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  semaphore sem;\n"
             "endmodule\n"));
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  barrier sem;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "declaration of type 'barrier' does not precede this reference to it", 2,
      "6.18"));
}

std::string InEachPlace(const std::string& use) {
  return "class my_obj;\n"
         "  int x;\n"
         "endclass\n"
         "function void in_unit();\n" +
         use +
         "endfunction\n"
         "package k;\n"
         "  function void in_package();\n" +
         use +
         "  endfunction\n"
         "endpackage\n"
         "class c;\n"
         "  function void in_class();\n" +
         use +
         "  endfunction\n"
         "endclass\n"
         "interface i;\n"
         "  function void in_interface();\n" +
         use +
         "  endfunction\n"
         "endinterface\n"
         "program p;\n"
         "  initial begin\n" +
         use +
         "  end\n"
         "endprogram\n"
         "module m;\n"
         "  i the_interface();\n"
         "  p the_program();\n"
         "  if (1) begin : g\n"
         "    initial begin\n" +
         use +
         "    end\n"
         "  end\n"
         "  task in_task();\n" +
         use +
         "  endtask\n"
         "  function automatic void in_function();\n" +
         use +
         "  endfunction\n"
         "endmodule\n";
}

TEST(StdPackageContents, EachMemberIsProvidedInEveryPlace) {
  for (const char* use :
       {"    automatic semaphore s = new(1);\n    s.put(1);\n",
        "    automatic mailbox b = new();\n    void'(b.num());\n",
        "    automatic int v;\n    void'(std::randomize(v));\n",
        "    automatic process r = process::self();\n    r.resume();\n",
        "    automatic weak_reference #(my_obj) w;\n    w = null;\n"}) {
    EXPECT_TRUE(ElabOk(InEachPlace(use))) << use;
  }
}

TEST(StdPackageContents, EachClassIsProvidedAsAVariableOfEveryPlace) {
  const std::string kVariables =
      "  semaphore s;\n"
      "  mailbox b;\n"
      "  process r;\n"
      "  weak_reference #(my_obj) w;\n";
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n" +
             kVariables + "package k;\n" + kVariables +
             "endpackage\n"
             "class c;\n" +
             kVariables +
             "endclass\n"
             "interface i;\n" +
             kVariables +
             "endinterface\n"
             "program p;\n" +
             kVariables +
             "endprogram\n"
             "module m;\n"
             "  i the_interface();\n"
             "  p the_program();\n"
             "  if (1) begin : g\n" +
             kVariables +
             "  end\n"
             "endmodule\n"));
}

}  // namespace
