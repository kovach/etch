#include <fstream>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common.h"
#include "sqlite3.h"

namespace {

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

void PrintRow(sqlite3_stmt* stmt) {
  int num_cols = sqlite3_column_count(stmt);

  for (int i = 0; i < num_cols; ++i) {
    if (i > 0) {
      std::cout << '|';
    }
    std::cout << sqlite3_column_text(stmt, i);
  }
  std::cout << std::endl;
}

}  // namespace

#define CHECK_ERR(c, msg)                                               \
  do {                                                                  \
    int tmp = (c);                                                      \
    if (tmp) {                                                          \
      std::cerr << "Error while " << msg << ": " << sqlite3_errstr(tmp) \
                << std::endl;                                           \
      exit(1);                                                          \
    }                                                                   \
  } while (false)

int main(int argc, char* argv[]) {
  char* zErrMsg = 0;
  int rc = SQLITE_OK;

  sqlite3* db;
  CHECK_ERR(sqlite3_initialize(), "initializing");

  int argi = 1;
  if (argi < argc && std::string_view(argv[argi]).starts_with(DB_PREFIX)) {
    std::string_view db_file(argv[1]);
    db_file.remove_prefix(DB_PREFIX.size());
    CHECK_ERR(sqlite3_open(db_file.data(), &db), "opening DB");
  } else {
    CHECK_ERR(sqlite3_open(":memory:", &db), "opening in-memory DB");
  }

  int query_idx = 1;

  for (; argi < argc; ++argi) {
    auto [reps, file] = ParseArg(argv[argi]);

    std::string filename(file);
    std::ifstream f(filename);
    std::stringstream file_ss;
    file_ss << f.rdbuf();
    std::string sql_str = std::move(file_ss).str();
    std::string_view sql_sv = sql_str;

    std::stringstream str_ss;
    str_ss << "q" << query_idx;
    std::string str_i = std::move(str_ss).str();

    if (reps > 0) {
      sqlite3_stmt* stmt = nullptr;
      time(
          [&]() {
            do {
              const char* remaining = nullptr;
              CHECK_ERR(sqlite3_prepare_v2(db, sql_sv.data(), sql_sv.size(),
                                           &stmt, &remaining),
                        "preparing " << filename);
              if (remaining) {
                sql_sv.remove_prefix(remaining - sql_sv.data());
              } else {
                sql_sv.remove_prefix(sql_sv.size());
              }
              sql_sv.remove_prefix(std::min(
                  sql_sv.find_first_not_of(" \t\r\v\n"), sql_sv.size()));
            } while (!stmt && !sql_sv.empty());
            return 0;
          },
          (str_i + " prep").c_str(), 1);
      if (!stmt) {
        continue;
      }
      time(
          [&]() {
            int res = sqlite3_step(stmt);
            for (; res != SQLITE_DONE; res = sqlite3_step(stmt)) {
              if (res == SQLITE_ROW) {
                PrintRow(stmt);
              } else {
                CHECK_ERR(res, "running " << filename);
              }
            }
            CHECK_ERR(sqlite3_reset(stmt), "resetting " << filename);
            return res;
          },
          str_i.c_str(), reps);

      CHECK_ERR(sqlite3_finalize(stmt), "finalizing " << filename);

      while (!sql_sv.empty()) {
        const char* remaining = nullptr;
        CHECK_ERR(sqlite3_prepare_v2(db, sql_sv.data(), sql_sv.size(), &stmt,
                                     &remaining),
                  "preparing " << filename);
        if (remaining) {
          sql_sv.remove_prefix(remaining - sql_sv.data());
        } else {
          sql_sv.remove_prefix(sql_sv.size());
        }

        if (stmt) {
          std::cerr << "Error while executing " << file
                    << ": more than one query in file" << std::endl;
          CHECK_ERR(sqlite3_finalize(stmt), "finalizing " << filename);
          return 1;
        }
      }
    } else {
      time(
          [&]() {
            do {
              sqlite3_stmt* stmt = nullptr;
              const char* remaining = nullptr;
              CHECK_ERR(sqlite3_prepare_v2(db, sql_sv.data(), sql_sv.size(),
                                           &stmt, &remaining),
                        "preparing " << filename);
              if (remaining) {
                sql_sv.remove_prefix(remaining - sql_sv.data());
              } else {
                sql_sv.remove_prefix(sql_sv.size());
              }
              sql_sv.remove_prefix(std::min(
                  sql_sv.find_first_not_of(" \t\r\v\n"), sql_sv.size()));

              int res = sqlite3_step(stmt);
              for (; res != SQLITE_DONE; res = sqlite3_step(stmt)) {
                if (res == SQLITE_ROW) {
                  PrintRow(stmt);
                } else {
                  CHECK_ERR(res, "running " << filename);
                }
              }

              CHECK_ERR(sqlite3_finalize(stmt), "finalizing " << filename);
            } while (!sql_sv.empty());
            return 0;
          },
          str_i.c_str(), 1);

    }
    ++query_idx;
  }
}
