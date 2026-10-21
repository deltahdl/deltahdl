// IEEE 1800-2023 §40.3.2.4 "$coverage_merge" and §40.3.2.5 "$coverage_save":
// the file a named coverage database is kept in, so that a database one run
// saves is there for a later run to merge. §40.3.2.5 leaves both the format and
// the mapping of a name to files to the tool; deltahdl keeps one text file per
// name, at the name's path under the state's database directory.
//
// The file opens with a header line, then names each instance of the design
// that saved it with its definition, which is how a merge tells a database of
// this design from one of another (§40.3.2.4), then the coverage types the
// database holds and the covered-item count each instance stood at:
//
//   deltahdl-coverage-database 1
//   instance top top
//   instance top.u1 leaf
//   type 21
//   covered top 21 2

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/coverage_control.h"

namespace delta {

namespace {

constexpr std::string_view kHeader = "deltahdl-coverage-database 1";

}  // namespace

std::string CoverageControlState::DatabasePath(const std::string& name) const {
  return database_directory_ + "/" + name;
}

std::string CoverageControlState::DesignSignature() const {
  std::vector<std::pair<std::string, std::string>> instances;
  for (const auto& entry : scopes_) {
    if (!entry.second.definition.empty()) {
      instances.emplace_back(entry.first, entry.second.definition);
    }
  }
  std::sort(instances.begin(), instances.end());
  std::string signature;
  for (const auto& [path, definition] : instances) {
    signature.append("instance ").append(path).append(" ");
    signature.append(definition).append("\n");
  }
  return signature;
}

bool CoverageControlState::WriteDatabaseFile(const std::string& name) const {
  if (database_directory_.empty()) return true;
  const CoverageDatabase& db = databases_.at(name);
  std::ofstream out(DatabasePath(name));
  out << kHeader << '\n' << DesignSignature();
  for (int type : db.coverage_types) out << "type " << type << '\n';
  for (const auto& [scope, counts] : db.covered_items) {
    for (const auto& [type, count] : counts) {
      out << "covered " << scope << ' ' << type << ' ' << count << '\n';
    }
  }
  out.flush();
  return static_cast<bool>(out);
}

bool CoverageControlState::ReadDatabaseFile(const std::string& name) {
  if (database_directory_.empty()) return false;
  std::ifstream in(DatabasePath(name));
  std::string line;
  if (!std::getline(in, line) || line != kHeader) return false;
  CoverageDatabase db;
  std::string signature;
  while (std::getline(in, line)) {
    std::istringstream fields(line);
    std::string tag;
    fields >> tag;
    if (tag == "instance") {
      signature += line + "\n";
      continue;
    }
    int type = 0;
    if (tag == "type" && fields >> type) {
      db.coverage_types.insert(type);
      continue;
    }
    std::string scope;
    std::int64_t count = 0;
    if (tag != "covered" || !(fields >> scope >> type >> count)) return false;
    db.covered_items[scope][type] = count;
  }
  db.from_this_design = signature == DesignSignature();
  databases_[name] = std::move(db);
  return true;
}

void CoverageControlState::RemoveDatabase(const std::string& name) {
  databases_.erase(name);
  if (!database_directory_.empty()) std::remove(DatabasePath(name).c_str());
}

}  // namespace delta
