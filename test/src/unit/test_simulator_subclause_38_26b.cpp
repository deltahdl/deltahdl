#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "helpers_run_files.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr PLI_UINT32 kFdBit = 0x80000000u;

struct NameResults {
  std::vector<std::string> names;
  const PLI_BYTE8* first_pointer = nullptr;
  const PLI_BYTE8* second_pointer = nullptr;
  std::string first_after_second;
  PLI_UINT32 checked_descriptor = 0;
};

NameResults results;

std::string NameOf(PLI_UINT32 cd) {
  const PLI_BYTE8* name = vpi_mcd_name(cd);
  return name == nullptr ? "<null>" : name;
}

class NameInARun : public RunFilesRun {
 protected:
  void SetUp() override {
    RunFilesRun::SetUp();
    results = {};
  }

  static PLI_INT32 NameInTurn(PLI_BYTE8*) {
    results.first_pointer = vpi_mcd_name(DescriptorIn("top.fd"));
    results.second_pointer = vpi_mcd_name(DescriptorIn("top.mcd"));
    results.first_after_second =
        results.first_pointer == nullptr ? "<null>" : results.first_pointer;
    return 0;
  }

  static PLI_INT32 NameBoth(PLI_BYTE8*) {
    results.names.push_back(NameOf(DescriptorIn("top.fd")));
    results.names.push_back(NameOf(DescriptorIn("top.mcd")));
    return 0;
  }

  static PLI_INT32 NameAnUnopenedFd(PLI_BYTE8*) {
    results.names.push_back(NameOf(kFdBit | 0x7000u));
    results.names.push_back(NameOf(DescriptorIn("top.fd")));
    return 0;
  }

  static PLI_INT32 NameAliasedPair(PLI_BYTE8*) {
    const PLI_UINT32 kMcds[] = {DescriptorIn("top.m1"), DescriptorIn("top.m2"),
                                DescriptorIn("top.m3")};
    const PLI_UINT32 kFds[] = {DescriptorIn("top.f1"), DescriptorIn("top.f2"),
                               DescriptorIn("top.f3")};
    for (const PLI_UINT32 kFd : kFds) {
      for (const PLI_UINT32 kMcd : kMcds) {
        if ((kFd & ~kFdBit) != kMcd) continue;
        results.checked_descriptor = kFd;
        results.names.push_back(NameOf(kFd));
        results.names.push_back(NameOf(kMcd));
        return 0;
      }
    }
    return 0;
  }

  static PLI_INT32 NameWithAVpiFile(PLI_BYTE8*) {
    const PLI_UINT32 kVpi = vpi_mcd_open(VpiText("v.txt"));
    results.names.push_back(NameOf(kVpi));
    results.names.push_back(NameOf(DescriptorIn("top.fd")));
    results.names.push_back(NameOf(DescriptorIn("top.mcd")));
    results.checked_descriptor = kVpi;
    return 0;
  }
};

constexpr const char* kBothForms =
    "module top; integer fd, mcd;\n"
    "  initial begin\n"
    "    fd = $fopen(\"fd.txt\", \"w\");\n"
    "    mcd = $fopen(\"mcd.txt\");\n"
    "    $name;\n"
    "  end\n"
    "endmodule\n";

TEST_F(NameInARun, ALaterCallOverwritesTheEarlierName) {
  RegisterTask("$name", &NameInTurn);
  Run(kBothForms);
  ASSERT_NE(results.first_pointer, nullptr);
  EXPECT_EQ(results.second_pointer, results.first_pointer);
  EXPECT_EQ(results.first_after_second, "mcd.txt");
}

TEST_F(NameInARun, FilesClosedByTheDesignAreNamedNothing) {
  RegisterTask("$name", &NameBoth);
  Run("module top; integer fd, mcd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"fd.txt\", \"w\");\n"
      "    mcd = $fopen(\"mcd.txt\");\n"
      "    $name;\n"
      "    $fclose(fd);\n"
      "    $fclose(mcd);\n"
      "    $name;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(results.names, (std::vector<std::string>{"fd.txt", "mcd.txt",
                                                     "<null>", "<null>"}));
}

TEST_F(NameInARun, AnFdNoOpenNamesIsNamedNothing) {
  RegisterTask("$name", &NameAnUnopenedFd);
  Run(kBothForms);
  EXPECT_EQ(results.names, (std::vector<std::string>{"<null>", "fd.txt"}));
}

TEST_F(NameInARun, AnFdIsNamedAsItsOwnFileNotAsTheMcdOfItsLowBits) {
  RegisterTask("$name", &NameAliasedPair);
  Run("module top; integer f1, f2, f3, m1, m2, m3;\n"
      "  initial begin\n"
      "    f1 = $fopen(\"f1.txt\", \"w\");\n"
      "    f2 = $fopen(\"f2.txt\", \"w\");\n"
      "    f3 = $fopen(\"f3.txt\", \"w\");\n"
      "    m1 = $fopen(\"m1.txt\");\n"
      "    m2 = $fopen(\"m2.txt\");\n"
      "    m3 = $fopen(\"m3.txt\");\n"
      "    $name;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(results.checked_descriptor, 0u);
  ASSERT_EQ(results.names.size(), 2u);
  EXPECT_EQ(results.names[0].front(), 'f');
  EXPECT_EQ(results.names[1].front(), 'm');
}

TEST_F(NameInARun, AVpiFileAndTheDesignsFilesEachNameTheirOwn) {
  RegisterTask("$name", &NameWithAVpiFile);
  Run(kBothForms);
  ASSERT_NE(results.checked_descriptor, 0u);
  EXPECT_NE(results.checked_descriptor & DescriptorIn("top.mcd"),
            results.checked_descriptor);
  EXPECT_EQ(results.names,
            (std::vector<std::string>{"v.txt", "fd.txt", "mcd.txt"}));
}

}  // namespace
}  // namespace delta
