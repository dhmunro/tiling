/**
 * @file rhombtile.js implements simple 2D geometry functions.
 * @author David H. Munro
 * @copyright David H. Munro 2023
 * @license MIT
 */

/*
 * Multigrid is a generalization of the deBruijn pentagrid (1981)
 * see https://www.math.brown.edu/reschwar/M272/pentagrid.pdf
 * This constructs a dual rhomb tiling for a completely arbitrary
 * multigrid - that is, any n>=3 grid normal directions and line
 * spacings.
 */
class Multigrid {
  constructor(directions, gamma) {
    let checkSort = false;
    if (Number.isInteger(directions)) {
      // Equally spaced in angle, equal grid spacings.
      let n = directions;
      directions = new Array(n).fill(Math.PI/n * ((n % 2)? 2 : 1))
        .map((da, j) => [Math.cos(j*da), Math.sin(j*da)]);
    } else if (Number.isFinite(directions[0])) {
      // Equally spaced in angle, unequal grid spacings listed.
      let n = directions.length;
      directions = new Array(n).fill(Math.PI/n * ((n % 2)? 2 : 1))
        .map((da, j) => [directions[j]*Math.cos(j*da),
                         directions[j]*Math.sin(j*da)]);
    } else {
      // Grid directions and spacings explicitly given as vectors.
      directions = Array.from(directions);
      checkSort = true;
    }
    let n = directions.length;
    let shifted = (n % 2) == 0 && n > 8 && !gamma;
    if (gamma == "zeros") [shifted, gamma] = [true, "zero"];
    if (n < 4 || directions[0].length != 2 ||
        !Number.isFinite(directions[0][0]) ||
        !Number.isFinite(directions[0][1])) {
      throw new Error("expected 4 or more 2D direction vectors");
    }
    if (gamma == "random") {
      gamma = new Array(n).fill(1).map(() => Math.random());
      let g0 = gamma.reduce((t, d) => t+d) / n;
      gamma = gamma.map((g, j) => g - g0);
    } else if (gamma == "perfect") {
      // produce tiling with perfect 2*n-fold azimuthal symmetry about (0,0)
      // after Lutfalla, https://arxiv.org/abs/2004.10128
      gamma = (n % 2)? 1/n : 0.5;
      gamma = new Array(n).fill(gamma);
    } else if (gamma == "zero" || gamma == "zeros") {
      // produce tiling with perfect 2*n-fold azimuthal symmetry about (0,0)
      // after Lutfalla, https://arxiv.org/abs/2004.10128
      gamma = new Array(n).fill(1.e-9);
    } else if (gamma) {
      if (gamma.length == n && Number.isFinite(gamma[0])) {
        gamma = Array.from(gamma);
      } else {
        throw new Error("expected gamma same length as directions");
      }
    }
    if (checkSort) {
      // Some constructions require that directions be sorted into
      // increasing angle (like the equally spaced constructions above).
      let angles = directions.map(([x, y]) => {
        let a = Math.atan2(y+1.e-12, x);
        if (a < 0) a += 2*Math.PI;
        return a;
      });
      directions = angles.map((a, j) => [a, directions[j]])
        .sort((a, b) => a[0]-b[0]).map(([_, d]) => d);
      if (gamma) {
        gamma = angles.map((a, j) => [a, gamma[j]])
          .sort((a, b) => a[0]-b[0]).map(([_, g]) => g);
      }
    }
    const norm2 = (x, y) => Math.sqrt(x**2+ y**2);
    const gzeta = Array.from(directions);
    const zeta = gzeta.map(([x, y]) => {  // zeta are normalized rhomb edges
      let r = norm2(x, y);
      return [x/r, y/r];
    });
    let skip = (n%2)? (n - 1)/2 : n - 1;
    let star = zeta.map((_, j, ez) => ez[(skip * j) % n]);
    if (!(n % 2)) star = star.map((e, j) => (j && !(j%2))? [-e[0], -e[1]] : e);
    if (!gamma) {
      let [qx, qy] = [3 - Math.E, Math.PI - 3];  // random offset
      gamma = star.map(e => e[0]*qx + e[1]*qy);
    }
    if (shifted) {
      gamma = gamma.map((gj, j) => zeta[j][0]*1234.56 + zeta[j][1]*789.01);
      gamma = gamma.map(gj => gj - Math.floor(gj));
    }
    // add a slight random twist to try to keep non-prime n grids regular
    if (n%2 == 0 || n%3 == 0) {
      let dgamma = gamma.map((_, j) => j*(1-0.01*j)*1.e-9);
      let dg0 = dgamma.reduce((t, d) => t+d) / n;
      dgamma = dgamma.map((dg, j) => dg - dg0);
      gamma = gamma.map((g, j) => g + dgamma[j]);
    }
    // mat = sum(gzeta.outer.zeta)
    let [xx, yy, xy] = gzeta.map(([x, y], j) =>
      [x*zeta[j][0], y*zeta[j][1], x*zeta[j][1]])
        .reduce(([xxt, yyt, xyt], [xx, yy, xy]) => [xxt+xx, yyt+yy, xyt+xy]);
    // psi = inverse(mat).dot.gzeta
    // inverse(mat) = [[yy, -xy], [-xy, xx]]/(xx*yy-xy*xy)
    const det = xx*yy - xy*xy;
    const psi = gzeta.map(([zx, zy]) =>
      [(yy*zx - xy*zy)/det, (xx*zy - xy*zx)/det]);
    // intersection (kr, ks) is at
    // p = ((ks-gammas)*psirp - (kr-gammar)*psisp) / (psirp.dot.psis)
    let pairs = new Array(n*(n-1)/2);
    let i = 0;
    for (let r=0 ; r<n-1 ; r+=1) {
      for (let s=r+1 ; s<n ; s+=1) {
        let [prx, pry] = psi[r];
        let [psx, psy] = psi[s];
        let rxs = prx*psy - pry*psx;
        let notrs = new Array(n).fill(1).map((_, j) => j)
          .filter(j => j!=r && j!=s);
        pairs[i++] = [[psy/rxs, -psx/rxs], [-pry/rxs, prx/rxs],
                      notrs, r, s];
      }
    }
    // Adding the zeta in sequence produces half of a 2*n sided polygon
    // with unit sides.  The center of this polygon and its maximum
    // radius determine the offset between grid intersections and dual
    // tiling vertices (center) and the padding required around a plot
    // limit box to guarantee all rhombs intersection the box are found
    // (radius).
    let [cx, cy] = zeta.reduce(([zxt, zyt], [zx, zy]) =>
                               [zxt+zx, zyt+zy]).map(v => 0.5*v);
    this.zetacen = [cx, cy];
    let radius = Math.sqrt(cx**2 + cy**2);
    [cx, cy] = [-cx, -cy];
    for (let j=0 ; j<n ; j+=1) {
      cx += zeta[j][0];
      cy += zeta[j][1];
      let cr = Math.sqrt(cx**2 + cy**2);
      if (cr > radius) radius = cr;
    }
    this.zetarad = radius;
    this.zeta = zeta;  // rhomb tile edges
    this.gamma = gamma;
    this.psi = psi;  // scaled grid lines are psi[j].dot.x + gamma[j] = kj
    // kj = ceil(psi.dot.p + gammaj)
    // (kr, ks) grid intersection is at
    // p = (kr - gammar)*pairs[0] + (ks - gammas)*pairs[1]
    this.pairs = pairs;
    // Group pairs by angle.
    let angles = pairs.map(([,,, r, s]) => {
      const [zrx, zry] = zeta[r];
      const [zsx, zsy] = zeta[s];
      return Math.abs(Math.atan2(zrx*zsy - zry*zsx,
                                 zrx*zsx + zry*zsy)) * 180/Math.PI;
    });
    angles = angles.map((a, ipair) => [a, ipair]);
    // Find rhomb (r,s) base angles that are unique to within one tenth degree.
    // Tenth degree is overkill, but nsym=24, e.g., has a bunch of half-integer
    // angles which can round either up or down, causing problems.
    let bases = [];
    let nbases = 0;
    for (let [a, ipair] of Array.from(angles).sort((a, b) => a[0] - b[0])) {
      let approx = Math.round(10*a);
      if (!nbases || approx != bases[nbases-1]) {
        bases.push(approx);
        pairs[ipair].push(nbases);  // record unique angle bin in pairs array
        nbases += 1;
      } else {
        pairs[ipair].push(nbases-1);  // this angle in previous bin
      }
    }
    // There may be fewer unique rhomb shapes than rhomb angles, because
    // either the angle or its supplement may be the (r,s) base angle.
    // (This never happens for equally spaced n odd, but always happens
    // for equally spaced n even.)  Given the index into bases, we want
    // to redirect any angles larger than 90 degrees to their
    // supplement if it exists in the bases angles list.
    let shapes = new Array(nbases).fill(1).map((_, j) => j);
    let nshapes = nbases;
    pairs.forEach(([,,,,, ib], ipair) => {
      if (shapes[ib] == ib) {
        let a = angles[ipair][0];
        if (a > 90.01) {
          let isupp = bases.indexOf(Math.round(10*(180-a)));
          if (isupp >= 0) {
            shapes[ib] = isupp;
            nshapes -= 1;
          }
        }
      }
    });
    this.angles = angles.map(([a, pair]) => a);
    this.bases = bases;  // sorted tenth degree angle bins
    this.shapes = shapes;  // indices into bases for smaller rhomb angle
    this.nshapes = nshapes;
  }

  pan(x, y, edge) {
    if (Array.isArray(x)) {
      [x, y] = x;
      if (!edge) edge = y;
    }
    if (edge) [x, y] = [x/edge, y/edge];
    const dg = this.psi.map(([psix, psiy]) => psix*x + psiy*y);
    this.gamma = this.gamma.map((gj, j) => gj - dg[j]);
  }

  // mg.crossLines(box, edge, tiler, liner);
  //   and executes tiler(mg, v, ipair, index, p)
  //   then executes liner(mg, endpts, r, kr)
  //   either can be undefined or null
  // liner can draw the grid lines, called after tiler to permit overlays
  // note that tiler may call mg.rhombverts to get all four vertices
  // tiler also passed dual grid intersection point
  // - these could be collected then drawn after liner
  //   to mark grid intersections (they may lie outside
  //   the corresponding rhomb, so drawing must be
  //   deferred until all rhombs drawn)
  crossLines(box, edge, tiler, liner) {
    this.edge = edge? edge : undefined;
    let lines;
    if (liner) lines = [];
    let pbox = this.bbox(box, edge);
    let [xmin, xmax, ymin, ymax] = pbox;
    let krnx = this.bounds(pbox);
    let {zeta, gamma, psi, pairs, zetacen} = this;
    let ipair = 0;  // index into this.pairs
    let n = this.psi.length;
    for (let r = 0; r < n; r += 1) {
      let endpts = [];
      let gammar = gamma[r];
      let [psirx, psiry] = psi[r];
      let [krn, krx] = krnx[r];
      // First loop on lines for each r:
      for (let kr = krn; kr <= krx; kr += 1) {
        let pts = [];
        if (psiry) {
          let [y0, m0] = [(kr - gammar)/psiry, psirx/psiry];
          let y = y0 - m0*xmin;
          if (y > ymin && y < ymax) pts.push([xmin, y]);
          y = y0 - m0*xmax;
          if (y > ymin && y < ymax) pts.push([xmax, y]);
        }
        if (pts.length < 2 && psirx) {
          let [x0, m0] = [(kr - gammar)/psirx, psiry/psirx];
          let x = x0 - m0*ymin;
          if (x > xmin && x < xmax) pts.push([x, ymin]);
          if (pts.length < 2) {
            x = x0 - m0*ymax;
            if (x > xmin && x < xmax) pts.push([x, ymax]);
          }
        }
        if (pts.length != 2) continue;
        if (liner) lines.push([r, kr, pts]);
        endpts.push([kr, pts]);
      }
      if (liner) lines.concat(endpts.map(([kr, pts]) => [r, kr, pts]));
      if (!tiler) continue;
      // Next loop on (r, s) pairs:
      for (let s = r+1; s < n; s += 1) {
        let gammas = gamma[s];
        let [psisx, psisy] = psi[s];
        // For each (r, s) loop over all kr lines:
        for (let [kr, [[x0, y0], [x1, y1]]] of endpts) {
          let [[dpxdkr, dpydkr], [dpxdks, dpydks], notrs] = pairs[ipair];
          // Begin by finding ksmin and ksmax from kr line endpts.
          // psi[s].dot.x + gamma[s] = ks
          let [ksn, ksx] = [psisx*x0 + psisy*y0 + gammas,
                            psisx*x1 + psisy*y1 + gammas];
          if (ksn > ksx) [ksn, ksx] = [ksx, ksn];
          [ksn, ksx] = [Math.ceil(ksn - 1.e-6), Math.floor(ksx + 1.e-6)];
          // For each kr line, loop over all ks line intersections.
          // p(kr,ks) = (kr-gammar)*dpdkr + (ks-gammas)*dpdks
          let [px, py] = [(kr - gammar)*dpxdkr + (ksn - gammas)*dpxdks,
                          (kr - gammar)*dpydkr + (ksn - gammas)*dpydks];
          for (let ks = ksn; ks <= ksx; ks += 1) {
            // (px, py) is the (kr, ks) grid intersection, find dual rhomb
            let sumlambda = 0;
            let [dpx, dpy] = notrs.map(j => {
              let [psijx, psijy] = psi[j];
              let lambdaj = psijx*px + psijy*py + gamma[j];  // psij.p+gammaj
              lambdaj = Math.ceil(lambdaj) - lambdaj;
              sumlambda += lambdaj;  // must sum to integer
              // should we detect lambdaj nearly 0 or 1 here?
              // if (lambdaj < 0.001 || lambdaj > 0.999) {
              //   console.log("lambdaj", lambdaj, j, r, s, kr, ks)
              // }
              let [zetajx, zetajy] = zeta[j];
              return [lambdaj*zetajx, lambdaj*zetajy];
            }).reduce(([dxt, dyt], [dx, dy]) => [dxt+dx, dyt+dy]);
            let v = [px + dpx - zetacen[0], py + dpy - zetacen[1]];
            let index = sumlambda;
            if (n % 2) index = Math.round(index);
            // if (Math.abs(sumlambda - index) > 1.e-6) {
            //   console.log(`WARNING: sum(lambdaj) = ${sumlambda}`)
            // }
            // (kr, ks) grid intersection [px, py] corresponds to
            // rhomb v, v+zeta[r], v+zeta[r]+zeta[s], v+zeta[s]
            // index = sum(lambdaj) remainders 0 < index < n-2
            let pxy = [px, py];
            if (edge) {
              v = [v[0]*edge, v[1]*edge];
              pxy = [px*edge, py*edge];
            }
            tiler(this, v, ipair, index, pxy);
            [px, py] = [px + dpxdks, py + dpydks];
          }
        }
        ipair += 1;
      }
    }
    if (liner) {
      // Make deferred calls to liner now.
      if (edge) lines = lines.map(([r, kr, [[x0, y0], [x1, y1]]]) =>
                [r, kr, [[x0*edge, y0*edge], [x1*edge, y1*edge]]]);
      for (let [r, kr, pts] of lines) liner(this, pts, r, kr);
    }
  }

  // If edge not supplied, will use edge from previous crossLines call,
  // which was used to scale v0 passed to tiler.
  rhombVerts(v0, ipair, edge) {
    let [,,, r, s] = this.pairs[ipair];
    let [[zrx, zry], [zsx, zsy]] = [this.zeta[r], this.zeta[s]];
    if (!edge) edge = this.edge;
    if (edge) [zrx, zry, zsx, zsy] = [zrx*edge, zry*edge, zsx*edge, zsy*edge];
    let v0vr = [v0[0] + zrx, v0[1] + zry];
    return [v0, v0vr, [v0vr[0] + zsx, v0vr[1] + zsy],
            [v0[0] + zsx, v0[1] + zsy]];
  }

  bbox([xmin, xmax, ymin, ymax], edge) {
    // Convert displayed bounding box to padded box in
    // system where rhombs have unit edge length.
    if (edge) {
      xmin /= edge;
      xmax /= edge;
      ymin /= edge;
      ymax /= edge;
    }
    let pad = this.zetarad;
    xmin -= pad;
    xmax += pad;
    ymin -= pad;
    ymax += pad;
    return [xmin, xmax, ymin, ymax];
  }

  bounds([xmin, xmax, ymin, ymax]) {
    // Return minimum and maximum kj values for any
    // vertex of a rhomb intersecting given bounding box.
    const {psi, gamma} = this;
    return psi.map(([psijx, psijy], j) => {
      let [kn, kx] = [[xmin, ymin], [xmax, ymin],
                      [xmin, ymax], [xmax, ymax]].map(
        ([x, y]) => psijx*x + psijy*y + gamma[j]
      ).reduce(([kmin, kmax], k) => 
        [(k<kmin)? k : kmin, (k > kmax)? k : kmax], [1.e35, -1.e35]);
      return [Math.floor(kn-1.e-6), Math.ceil(kx+1.e-6)];
    });
  }
}
