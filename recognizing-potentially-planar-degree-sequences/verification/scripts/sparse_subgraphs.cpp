// Enumerate positive degree histograms on the two sparse boundary layers.
// Read plantri -a records of one order (2 through 10) on standard input.
// Build: c++ -O3 -std=c++17 sparse_subgraphs.cpp -o /tmp/sparse_subgraphs
// Run the comparison with sparse_subgraphs.py.
#include <array>
#include <cstdint>
#include <iostream>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Histogram = std::uint64_t;

// Four bits per multiplicity suffice for all orders supported here.
Histogram unit(int degree) { return Histogram{1} << (4 * degree); }

struct Host {
    int order;
    std::vector<std::pair<int, int>> edges;
    std::array<int, 10> degrees{};

    void visit(int remaining, int edge_count, Histogram histogram,
               std::set<Histogram>& found) {
        if (histogram & 15) return;  // An isolated vertex survives every further deletion.
        if (remaining == 0) {
            int leaves = (histogram >> 4) & 15;
            int delta = 4 * order - 2 * leaves - 2 * edge_count;
            if (delta == 0 || delta == 2) found.insert(histogram);
            return;
        }
        auto [u, v] = edges[remaining - 1];
        visit(remaining - 1, edge_count, histogram, found);

        for (int vertex : {u, v}) {
            histogram -= unit(degrees[vertex]);
            --degrees[vertex];
            histogram += unit(degrees[vertex]);
        }
        visit(remaining - 1, edge_count - 1, histogram, found);
        ++degrees[u];
        ++degrees[v];
    }
};

Host read_host(const std::string& line) {
    Host host{};
    std::istringstream record(line);
    std::string rotation, extra;
    if (!(record >> host.order >> rotation) || host.order < 2 || host.order > 10 ||
        (record >> extra)) throw std::runtime_error("invalid plantri ASCII record");
    std::array<std::array<bool, 10>, 10> adjacent{};
    std::istringstream rows(rotation);
    std::string neighbors;
    for (int u = 0; u < host.order; ++u) {
        if (!std::getline(rows, neighbors, ',') || neighbors.empty())
            throw std::runtime_error("missing neighbor row");
        for (char c : neighbors) {
            int v = c - 'a';
            if (v < 0 || v >= host.order || v == u || adjacent[u][v])
                throw std::runtime_error("invalid neighbor");
            adjacent[u][v] = true;
            ++host.degrees[u];
            if (u < v) host.edges.emplace_back(u, v);
        }
    }
    if (std::getline(rows, neighbors, ',')) throw std::runtime_error("extra neighbor row");
    for (int u = 0; u < host.order; ++u)
        for (int v = u + 1; v < host.order; ++v)
            if (adjacent[u][v] != adjacent[v][u])
                throw std::runtime_error("asymmetric neighbor lists");
    int expected = host.order == 2 ? 1 : 3 * host.order - 6;
    if (static_cast<int>(host.edges.size()) != expected)
        throw std::runtime_error("incorrect edge count for a maximal planar host");
    return host;
}

int main() {
    std::set<Histogram> found;
    std::string line;
    int order = 0;
    try {
        while (std::getline(std::cin, line)) {
            auto host = read_host(line);
            if (order && order != host.order) throw std::runtime_error("mixed orders");
            order = host.order;
            Histogram histogram = 0;
            for (int i = 0; i < order; ++i) histogram += unit(host.degrees[i]);
            int edges = static_cast<int>(host.edges.size());
            host.visit(edges, edges, histogram, found);
        }
        if (!order) throw std::runtime_error("empty host input");
        for (auto histogram : found) std::cout << histogram << '\n';
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
