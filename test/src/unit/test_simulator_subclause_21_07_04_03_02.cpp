#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vcd_dump_run.h"

namespace delta {
namespace {

class ExtendedVcdDriversSim : public VcdDumpRunTestBase {
 protected:
  std::string RunPortVcd(const std::string& src) {
    return RunVcdDump(src,
                      {.scope = "t",
                       .registration = VcdSignalRegistration::kContextFiltered,
                       .extended = true});
  }

  static std::vector<std::string> Tokens(const std::string& line) {
    std::vector<std::string> out;
    size_t i = 0;
    while (i < line.size()) {
      while (i < line.size() && (line[i] == ' ' || line[i] == '\t')) ++i;
      size_t start = i;
      while (i < line.size() && line[i] != ' ' && line[i] != '\t') ++i;
      if (i > start) out.push_back(line.substr(start, i - start));
    }
    return out;
  }

  static std::vector<std::string> Lines(const std::string& content) {
    std::vector<std::string> out;
    size_t pos = 0;
    while (pos <= content.size()) {
      size_t nl = content.find('\n', pos);
      if (nl == std::string::npos) {
        if (pos < content.size()) out.push_back(content.substr(pos));
        break;
      }
      out.push_back(content.substr(pos, nl - pos));
      pos = nl + 1;
    }
    return out;
  }

  static std::string IdentOnPortLine(const std::vector<std::string>& tokens,
                                     const std::string& name) {
    if (tokens.size() < 2 || tokens[0] != "$var" || tokens[1] != "port") {
      return "";
    }
    for (size_t k = 2; k + 1 < tokens.size(); ++k) {
      if (tokens[k] == name && !tokens[k - 1].empty() &&
          tokens[k - 1][0] == '<') {
        return tokens[k - 1];
      }
    }
    return "";
  }

  static std::string IdentFor(const std::string& content,
                              const std::string& name) {
    for (auto& line : Lines(content)) {
      std::string ident = IdentOnPortLine(Tokens(line), name);
      if (!ident.empty()) return ident;
    }
    return "<none>";
  }

  std::string PortRecord(const std::string& content, const std::string& name) {
    std::string ident = IdentFor(content, name);
    if (ident == "<none>") return "<no-ident>";
    std::string found = "<no-change>";
    for (auto& line : Lines(content)) {
      if (line.empty() || line[0] != 'p') continue;
      auto t = Tokens(line);
      if (t.size() != 2 || t[1] != ident) continue;
      std::string body = t[0].substr(1);
      if (body.size() < 3) return "<malformed>";
      std::string value = body.substr(0, body.size() - 2);
      std::string strength = body.substr(body.size() - 2);
      found = value;
      found += '|';
      found += strength;
    }
    return found;
  }
};

TEST_F(ExtendedVcdDriversSim, PrimitiveDriverDumpsActivePort) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic a;\n"
      "  wire w;\n"
      "  buf (w, a);\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(PortRecord(content, "w"), "1|06") << content;
}

TEST_F(ExtendedVcdDriversSim, ContinuousAssignmentDriverDumpsActivePort) {
  auto content = RunPortVcd(
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_EQ(PortRecord(content, "w"), "1|06") << content;
}

TEST_F(ExtendedVcdDriversSim,
       ForceProceduralContinuousAssignmentDumpsActivePort) {
  auto content = RunPortVcd(
      "module t;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    force w = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(PortRecord(content, "w"), "1|06") << content;
}

TEST_F(ExtendedVcdDriversSim,
       AssignProceduralContinuousAssignmentDumpsActivePort) {
  auto content = RunPortVcd(
      "module t;\n"
      "  logic v;\n"
      "  initial begin\n"
      "    $dumpports;\n"
      "    assign v = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(PortRecord(content, "v"), "1|66") << content;
}

TEST_F(ExtendedVcdDriversSim, UndrivenPortIsNotAnActiveDriver) {
  auto content = RunPortVcd(
      "module t;\n"
      "  wire w;\n"
      "  initial $dumpports;\n"
      "endmodule\n");
  EXPECT_EQ(PortRecord(content, "w"), "F|00") << content;
}

}  // namespace
}  // namespace delta
