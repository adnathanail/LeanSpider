// Based on pyzx's zx_viewer.inline.js (Apache 2.0)
// Modified: added click-to-highlight-neighbours, adapted for ES module use.

export function showGraph(container, graph, width, height, scale, node_size, colors, show_labels) {
    var d3 = window.d3;
    var ntab = {};
    var groundOffset = 2.5 * node_size;

    function nodeColor(t) {
        if (t == 0) return colors['boundary'];
        else if (t == 1) return colors['Z'];
        else if (t == 2) return colors['X'];
        else if (t == 3) return colors['H'];
        else if (t == 4) return colors['W'];
        else if (t == 5) return colors['Walt'];
        else if (t == 6) return colors['Zalt'];
    }

    function edgeColor(t) {
        if (t == 1) return colors['edge'];
        else if (t == 2) return colors['Hedge'];
        else if (t == 3) return colors['Xedge'];
    }

    graph.nodes.forEach(function(d) {
        ntab[d.name] = d;
        d.selected = false;
        d.previouslySelected = false;
        d.nhd = [];
    });

    graph.links.forEach(function(d) {
        var s = ntab[d.source];
        var t = ntab[d.target];
        d.source = s;
        d.target = t;
        s.nhd.push(t);
        t.nhd.push(s);
    });

    // --- HIGHLIGHT STATE ---
    var highlightedNode = null;

    function updateHighlight() {
        if (highlightedNode == null) {
            // No highlight — full opacity everywhere
            node.attr("opacity", 1);
            link.attr("opacity", 1);
        } else {
            var hn = highlightedNode;
            var nhdNames = new Set(hn.nhd.map(function(n) { return n.name; }));
            nhdNames.add(hn.name);

            node.attr("opacity", function(d) {
                return nhdNames.has(d.name) ? 1 : 0.15;
            });
            link.attr("opacity", function(d) {
                var sName = d.source.name;
                var tName = d.target.name;
                // Show edge if both endpoints are in the highlighted set
                return (nhdNames.has(sName) && nhdNames.has(tName)) ? 1 : 0.08;
            });
        }
    }

    // --- SVG SETUP ---
    var svg = d3.select(container)
        .append("svg")
        .attr("style", "max-width: none; max-height: none")
        .attr("width", width)
        .attr("height", height);

    var link = svg.append("g")
        .attr("class", "link")
        .selectAll("path")
        .data(graph.links)
        .enter().append("path")
        .attr("stroke", function(d) { return edgeColor(d.t); })
        .attr("fill", "transparent")
        .attr("style", "stroke-width: 1.5px");

    var node = svg.append("g")
        .attr("class", "node")
        .selectAll("g")
        .data(graph.nodes)
        .enter().append("g")
        .attr("transform", function(d) {
            return "translate(" + d.x + "," + d.y + ")";
        });

    // Draw ground symbols
    node.filter(function(d) { return d.ground; })
        .append("path")
        .attr("stroke", "black")
        .attr("style", "stroke-width: 1.5px")
        .attr("fill", "none")
        .attr("d", "M 0 0 L 0 " + groundOffset)
        .attr("class", "selectable");

    // Circles for spiders and boundaries (not H-boxes)
    node.filter(function(d) { return d.t != 3 && d.t != 5 && d.t != 6; })
        .append("circle")
        .attr("r", function(d) {
            if (d.t == 0) return 0.5 * node_size;
            else if (d.t == 4) return 0.25 * node_size;
            else return node_size;
        })
        .attr("fill", function(d) { return nodeColor(d.t); })
        .attr("stroke", "black")
        .attr("class", "selectable");

    // H-box rectangles
    var hbox = node.filter(function(d) { return d.t == 3; });
    hbox.append("rect")
        .attr("x", -0.75 * node_size).attr("y", -0.75 * node_size)
        .attr("width", node_size * 1.5).attr("height", node_size * 1.5)
        .attr("fill", function(d) { return nodeColor(d.t); })
        .attr("stroke", "black")
        .attr("class", "selectable");

    // Z-box squares (t == 6)
    node.filter(function(d) { return d.t == 6; })
        .append("rect")
        .attr("x", -0.75 * node_size).attr("y", -0.75 * node_size)
        .attr("width", node_size * 1.5).attr("height", node_size * 1.5)
        .attr("fill", function(d) { return nodeColor(d.t); })
        .attr("stroke", "black")
        .attr("class", "selectable");

    // Triangle for W_ALT (t == 5)
    node.filter(function(d) { return d.t == 5; })
        .append("path")
        .attr("d", "M 0 0 L " + node_size + " " + node_size + " L -" + node_size + " " + node_size + " Z")
        .attr("fill", function(d) { return nodeColor(d.t); })
        .attr("stroke", "black")
        .attr("class", "selectable")
        .attr("transform", "translate(" + (-node_size / 2) + ", 0) rotate(-90)");

    // Phase labels
    node.filter(function(d) { return d.phase != ''; })
        .append("text")
        .attr("y", 0.7 * node_size + 14)
        .text(function(d) { return d.phase; })
        .attr("text-anchor", "middle")
        .attr("font-size", "12px")
        .attr("font-family", "monospace")
        .attr("fill", "#00d")
        .attr("style", "pointer-events: none; user-select: none;");

    // Node ID labels
    if (show_labels) {
        node.append("text")
            .attr("y", -0.7 * node_size - 8)
            .text(function(d) { return d.name; })
            .attr("text-anchor", "middle")
            .attr("font-size", "10px")
            .attr("font-family", "monospace")
            .attr("fill", "#999")
            .attr("style", "pointer-events: none; user-select: none;");
    }

    // --- AUTO H-BOX POSITIONING ---
    function update_hboxes() {
        var pos = {};
        hbox.attr("transform", function(d) {
            var x = 0, y = 0, sz = 0;
            for (var i = 0; i < d.nhd.length; ++i) {
                if (d.nhd[i].t != 3) {
                    sz++;
                    x += d.nhd[i].x;
                    y += d.nhd[i].y;
                }
            }
            var offset = 0.25 * scale;
            if (sz != 0) {
                x = (x / sz) + offset;
                y = (y / sz) - offset;
                while (pos[[x, y]]) { x += offset; }
                d.x = x;
                d.y = y;
                pos[[x, y]] = true;
            }
            return "translate(" + d.x + "," + d.y + ")";
        });
    }
    update_hboxes();

    // --- EDGE CURVES (handles parallel edges) ---
    var link_curve = function(d) {
        var x1 = d.source.x, x2 = d.target.x, y1 = d.source.y, y2 = d.target.y;
        if (x1 == x2 && y1 == y2 && d.num_parallel == 1) {
            // Self-loop (single)
            var cx1 = x1 - 40, cy1 = y1 - 40, cx2 = x1 + 40, cy2 = y1 - 40;
            return "M " + x1 + " " + y1 + " C " + cx1 + " " + cy1 + ", " + cx2 + " " + cy2 + ", " + x2 + " " + y2;
        } else if (x1 == x2 && y1 == y2) {
            // Self-loop (multiple)
            var pos = d.index + 1;
            var cx1 = x1 - 20 - pos * 10, cy1 = y1 - 20 - pos * 10;
            var cx2 = x1 + 20 + pos * 10, cy2 = y1 - 20 - pos * 10;
            return "M " + x1 + " " + y1 + " C " + cx1 + " " + cy1 + ", " + cx2 + " " + cy2 + ", " + x2 + " " + y2;
        } else if (d.num_parallel == 1) {
            return "M " + x1 + " " + y1 + " L " + x2 + " " + y2;
        } else {
            // Parallel edges — spread as bezier arcs
            var dx = x2 - x1, dy = y2 - y1;
            var midx = 0.5 * (x1 + x2), midy = 0.5 * (y1 + y2);
            var p = (d.index / (d.num_parallel - 1)) - 0.5;
            var cx = midx - p * dy;
            var cy = midy + p * dx;
            return "M " + x1 + " " + y1 + " Q " + cx + " " + cy + ", " + x2 + " " + y2;
        }
    };
    link.attr("d", link_curve);

    // --- DRAG ---
    node.call(d3.drag().on("drag", function(d) {
        var dx = d3.event.dx;
        var dy = d3.event.dy;
        node.filter(function(d) { return d.selected; })
            .attr("transform", function(d) {
                d.x += dx;
                d.y += dy;
                return "translate(" + d.x + "," + d.y + ")";
            });
        update_hboxes();
        link.filter(function(d) { return d.source.selected || d.target.selected || d.source.t == 3; })
            .attr("d", link_curve);
    }));

    // --- CLICK TO HIGHLIGHT NEIGHBOURS ---
    node.on("click", function(d) {
        d3.event.stopPropagation();
        if (highlightedNode === d) {
            // Click same node again — deselect
            highlightedNode = null;
        } else {
            highlightedNode = d;
        }
        // Also mark as selected for drag
        node.each(function(p) { p.selected = (p === highlightedNode); });
        node.selectAll(".selectable").attr("style", function(p) {
            return p.selected ? "stroke-width: 2px; stroke: #00f" : "stroke-width: 1.5px";
        });
        updateHighlight();
    });

    // Click on background to deselect
    svg.on("click", function() {
        highlightedNode = null;
        node.each(function(p) { p.selected = false; });
        node.selectAll(".selectable").attr("style", "stroke-width: 1.5px");
        updateHighlight();
    });
}
