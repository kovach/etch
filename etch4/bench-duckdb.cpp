#include <fstream>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common.h"
#include "duckdb/duckdb.hpp"

namespace {

namespace d = duckdb;

std::string_view DB_PREFIX = "db:";

std::pair<int, std::string_view> ParseArg(std::string_view s) {
  int reps = -1;
  bool found = false;

  for (int i = 0; i < s.size(); ++i) {
    if ('0' <= s[i] && s[i] <= '9') {
      found = true;
    } else if (s[i] == ':' && found) {
      reps = std::stoul(std::string(s.substr(0, i)));
      s.remove_prefix(i + 1);
      break;
    } else {
      break;
    }
  }

  return {reps, s};
}

}  // namespace

int main(int argc, char* argv[]) {
  std::unique_ptr<d::DuckDB> db_ptr;

  int argi = 1;
  if (argi < argc && std::string_view(argv[argi]).starts_with(DB_PREFIX)) {
    std::string_view db_file(argv[1]);
    db_file.remove_prefix(DB_PREFIX.size());
    db_ptr = std::make_unique<d::DuckDB>(std::string(db_file));
  } else {
    db_ptr = std::make_unique<d::DuckDB>();
  }

  d::DuckDB& db = *db_ptr;
  d::Connection con(db);

  int query_idx = 1;

  for (; argi < argc; ++argi) {
    auto [reps, file] = ParseArg(argv[argi]);

    std::ifstream f((std::string(file)));
    std::stringstream file_ss;
    file_ss << f.rdbuf();
    std::string sql_str = std::move(file_ss).str();

    std::stringstream str_ss;
    str_ss << "q" << query_idx;
    std::string str_i = std::move(str_ss).str();

    if (reps > 0) {
      std::unique_ptr<d::PreparedStatement> prepare;
      time(
          [&]() {
            prepare = con.Prepare(sql_str);
            return 0;
          },
          (str_i + " prep").c_str(), 1);

      if (prepare->HasError()) {
        std::cout << "Preparing " << file << " failed: " << prepare->GetError()
                  << '\n';
        return 1;
      }

      std::unique_ptr<d::QueryResult> res;
      std::vector<d::Value> values;
      res = prepare->Execute(values, /*allow_stream_result=*/false);
      res = prepare->Execute(values, /*allow_stream_result=*/false);

      time(
          [&]() {
            res = prepare->Execute(values,
                                   /*allow_stream_result=*/false);
            return 0;
          },
          str_i.c_str(), reps);
      std::cout << res->ToString() << '\n';
    } else {
      std::unique_ptr<d::MaterializedQueryResult> res;
      time(
          [&]() {
            res = con.Query(sql_str);
            return 0;
          },
          str_i.c_str(), 1);
      std::cout << res->ToString() << '\n';
    }

    ++query_idx;
  }
}
