#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "fixture_vcd_dump_from_source.h"
#include "helpers_text_lines.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

class ExtendedVcdFromSource : public VcdDumpFromSourceTestBase {
 protected:
  static std::string LastSegment(const std::string& scope) {
    auto dot = scope.rfind('.');
    return dot == std::string::npos ? scope : scope.substr(dot + 1);
  }

  static std::string Design(const std::string& calls) {
    return "module leaf(input l);\n"
           "endmodule\n"
           "module m(input a, output b);\n"
           "  logic body_var;\n"
           "  assign b = a;\n"
           "  leaf lf(a);\n"
           "endmodule\n"
           "module m2(input c);\n"
           "endmodule\n"
           "module t;\n"
           "  logic a = 1'b0;\n"
           "  logic c = 1'b0;\n"
           "  wire b;\n"
           "  integer seen, held, rfd;\n"
           "  string line;\n"
           "  string sname = \"one.vcd\";\n"
           "  logic [8*7:1] iname = \"one.vcd\";\n"
           "  m u(a, b);\n"
           "  m2 v(c);\n"
           "  initial begin\n" +
           calls +
           "  end\n"
           "endmodule\n";
  }

  static std::string CountPortRecordsInto(const std::string& file) {
    return "    seen = 0;\n"
           "    rfd = $fopen(\"" +
           file +
           "\", \"r\");\n"
           "    while ($fgets(line, rfd)) if (line[0] == \"p\") seen++;\n"
           "    $fclose(rfd);\n";
  }

  std::string Run(const std::string& calls) {
    RunSource(Design(calls));
    return DumpFile("one.vcd");
  }

  int64_t Seen() {
    delta::Variable* var = f_.ctx.FindVariable("seen");
    return var == nullptr ? -1 : static_cast<int64_t>(var->value.ToUint64());
  }

  static std::string Declared(const std::string& content) {
    std::vector<std::string> scopes;
    std::string names;
    for (const auto& line : AllLines(content)) {
      auto toks = Tokens(line);
      if (toks.size() >= 3 && toks[0] == "$scope") {
        scopes.push_back(LastSegment(toks[2]));
      }
      if (!toks.empty() && toks[0] == "$upscope" && !scopes.empty()) {
        scopes.pop_back();
      }
      if (toks.size() < 6 || toks[0] != "$var") continue;
      if (!names.empty()) names += ' ';
      names += (scopes.empty() ? std::string() : scopes.back() + ".") +
               toks[toks.size() - 2];
    }
    return names;
  }

  static std::string PortCode(const std::string& content,
                              const std::string& scope,
                              const std::string& name) {
    std::string inside;
    for (const auto& line : AllLines(content)) {
      auto toks = Tokens(line);
      if (toks.size() >= 3 && toks[0] == "$scope")
        inside = LastSegment(toks[2]);
      if (toks.size() == 6 && toks[0] == "$var" && inside == scope &&
          toks[4] == name) {
        return toks[3];
      }
    }
    return "<undeclared>";
  }

  static std::string Section(const std::string& content,
                             const std::string& keyword) {
    auto start = content.find("\n" + keyword + "\n");
    if (start == std::string::npos) return "<no " + keyword + ">";
    auto end = content.find("$end", start);
    return content.substr(start, end - start);
  }

  static size_t CountSections(const std::string& content,
                              const std::string& keyword) {
    size_t n = 0;
    for (const auto& line : AllLines(content)) {
      if (line == keyword) ++n;
    }
    return n;
  }

  static std::string StatesFor(const std::string& text,
                               const std::string& code) {
    std::string states;
    for (const auto& line : AllLines(text)) {
      auto toks = Tokens(line);
      if (toks.size() != 2 || toks[1] != code || line.size() < 4 ||
          line[0] != 'p') {
        continue;
      }
      states += toks[0].substr(1, toks[0].size() - 3);
    }
    return states;
  }
};
