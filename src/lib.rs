#![allow(non_snake_case)]

const MAXN : usize = 64;              // the maximum number of vertices; see above
const MAXE : usize = (6 * MAXN - 12); // the maximum number of oriented edges
const MAXF : usize = (2 * MAXN - 4);  // the maximum number of faces

//typedef struct e /* The data type used for edges */
//{
//int start;         /* vertex where the edge starts */
//int end;           /* vertex where the edge ends */
//int rightface;     /* face on the right side of the edge
//                          note: only valid if make_dual() called */
//struct e *prev;    /* previous edge in clockwise direction */
//struct e *next;    /* next edge in clockwise direction */
//struct e *invers;  /* the edge that is inverse to this one */
//struct e *min;     /* the least of e and e->invers */
//int mark,index;    /* two ints for temporary use;
//                          Only access mark via the MARK macros. */
//int left_facesize; /* size of the face in prev-direction of the edge.
//        		  Only used for -p option. */
//} EDGE;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Edge {
    start : usize,
    end   : usize
}

impl Edge {
    #[inline]
    pub fn start(&self) -> usize {
        self.start
    }

    #[inline]
    pub fn end(&self) -> usize {
        self.end
    }

    #[inline]
    pub fn next(&self) -> Edge {
        *self
    }

    #[inline]
    pub fn prev(&self) -> Edge {
        *self
    }

    #[inline]
    pub fn invers(&self) -> Edge {
        *self
    }
}


const NUMEDGES : usize = (24 + 70*MAXN);

pub struct Cxt {
    nv    : usize,            // number of vertices; they are 0..nv-1
    ne    : usize,             // number of directed edges (at most 6*nv-12)
    edges : [Edge; NUMEDGES],

    degree    : [usize; MAXN],  // the degrees of the vertices
    firstedge : [Edge; MAXN],   /* pointer to arbitrary edge out of vertex i. */
                                /* This pointer may change during the run, so all one can rely on is that
                                    at any point it is "some" edge out of i */

    maxnv      : usize,          /* order of output graphs */
    res        : usize,
    mod_       : usize,        /* res/mod from command line (default 0/1) */
    splitlevel : usize,
    splitcount : usize,     /* used for res/mod splitting */
}


//static cxt : Cxt =
//    Cxt { nv        : 0
//        , ne        : 0
//        , edges     : [Edge { start : 0, end : 0 }; NUMEDGES]
//        , degree    : [0; MAXN]
//        , firstedge : [Edge { start : 0, end : 0 }; MAXN]
//        , maxnv     : 12
//        , res        : 0
//        , mod_       : 1
//        , splitlevel : 0
//        , splitcount : 0
//        };



// Tests whether starting from a given edge and constructing the code in
// "->next" direction, an automorphism or even a better representation
// can be found. Returns 0 for failure, 1 for an automorphism and 2 for
// a better representation.  This function exits as soon as a better
// representation is found. A function that computes and returns the
// complete better representation can work pretty similar.*/
fn testcanon(cxt : &mut Cxt, givenedge : Edge, representation : &[usize], colour : &[usize]) -> i32 {
    let mut startedge = [givenedge; MAXN+1]; // startedge[i] is the starting edge for exploring the vertex with the number i+1
    let mut number = [0; MAXN]; // The new numbers of the vertices, starting at 1 in order to have "0" as a possibility to mark ends of lists and not yet given numbers
    number[givenedge.start()] = 1;

    let mut last_number = 1;
    if givenedge.start() != givenedge.end() {
        number[givenedge.end()] = 2;
        last_number = 2;
        startedge[1] = givenedge.invers();
    }

    let mut actual_number = 1;
    let mut temp = givenedge;
    let mut rep_id = 0;

     /* A representation is a clockwise ordering of all neighbours ended with a 0.
       The neighbours are numbered in the order that they are reached by the BFS
       procedure. In case a vertex is reached for the first time, not the (new)
       number of the vertex is listed, but its colour. When the list around a
       vertex is finished, it is ended with a 0. Since the colours can be
       distinguished from the vertices (requirement for the colour function), the
       adjacency list can be reconstructed: Every time a colour is listed, its
       number would be the smallest number not given yet.
       Since the edges when a vertex is reached for the first time are remembered,
       for these edges we in fact have more than just the vertex information -- for
       these edges we also have the exact information which edge occurs in the
       cyclic order. This makes the routine work also for double edges.

       Since every representation starts with the colour of vertex 2, which is
       the same colour all the time, we do not have to store that.

       In case of a loop as the starting point, the colour of 1 is omitted.
       Nevertheless also in this case it cannot be mixed up with a non-loop
       starting point, since the number of times a colour occurs is larger
       for loop starters than for non-loop starters.

       Every first entry in a new clockwise ordering (the starting point of the
       edge it was numbered from is determined by the entries before (the first
       time it occurs in the list to be exact), so this is not given either.
       The K4 could be denoted  c3 c4 0 4 3 0 2 3 0 3 2 0 if ci is the colour
       of vertex i.  Note that the colour of vertex 1 is -- by definition --
       always the smallest one */

    while last_number < cxt.nv {
        // this loop marks all edges around temp->origin.
        let mut run = temp.next();
        while run != temp {
            let mut vertex = run.end();
            if number[vertex] == 0 {
                startedge[last_number] = run.invers();
                last_number += 1;
                number[vertex] = last_number;
                vertex = colour[vertex];
            } else { vertex = number[vertex]; }

            if vertex > representation[rep_id] { return 0; }
            if vertex < representation[rep_id] { return 2; }
            rep_id += 1;

            run = run.next();
        }

         /* check whether representation[] is also at the end of a cyclic list */
        if representation[rep_id] != 0 {
            return 2;
        }
        rep_id += 1;

        temp = startedge[actual_number];
        actual_number += 1;
    }

    // Now we know that all numbers have been given
    while actual_number <= cxt.nv {
        let mut run = temp.next();
        while run != temp {
            let vertex = number[run.end()];

            if vertex > representation[rep_id] { return 0; }
            if vertex < representation[rep_id] { return 2; }
            rep_id += 1;

            run = run.next();
        }

         /* check whether representation[] is also at the end of a cyclic list */
        if representation[rep_id] != 0 {
            return 2;
        }
        rep_id += 1;

        temp = startedge[actual_number];
        actual_number += 1;
    }

    1
}


// Tests whether starting from a given edge and constructing the code in
// "->prev" direction, an automorphism or even a better representation can
// be found. Comments see testcanon -- it is exactly the same except for
// the orientation
fn testcanon_mirror(cxt : &mut Cxt, givenedge : Edge, representation : &[usize], colour : &[usize]) -> i32 {
    let mut startedge = [givenedge; MAXN+1];
    let mut number = [0; MAXN];
    number[givenedge.start()] = 1;

    let mut last_number = 1;
    if givenedge.start() != givenedge.end() {
        number[givenedge.end()] = 2;
        last_number = 2;
        startedge[1] = givenedge.invers();
    }

    let mut actual_number = 1;
    let mut temp = givenedge;
    let mut rep_id = 0;

    while last_number < cxt.nv {
        let mut run = temp.prev();
        while run != temp {
            let mut vertex = run.end();
            if number[vertex] == 0 {
                startedge[last_number] = run.invers();
                last_number += 1;
                number[vertex] = last_number;
                vertex = colour[vertex];
            } else { vertex = number[vertex]; }

            if vertex > representation[rep_id] { return 0; }
            if vertex < representation[rep_id] { return 2; }
            rep_id += 1;

            run = run.prev();
        }

        if representation[rep_id] != 0 {
            return 2;
        }
        rep_id += 1;

        temp = startedge[actual_number];
        actual_number += 1;
    }

    while actual_number <= cxt.nv {
        let mut run = temp.prev();
        while run != temp {
            let vertex = number[run.end()];

            if vertex > representation[rep_id] { return 0; }
            if vertex < representation[rep_id] { return 2; }
            rep_id += 1;

            run = run.prev();
        }

        if representation[rep_id] != 0 {
            return 2;
        }
        rep_id += 1;

        temp = startedge[actual_number];
        actual_number += 1;
    }

    1
}


// Tests whether starting from a given edge and constructing the code in
// "->next" direction, an automorphism or even a better representation can
// be found. A better representation will be completely constructed and
// returned in "representation".  It works pretty similar to testcanon except
// for obviously necessary changes, so for extensive comments see testcanon
fn testcanon_first_init(cxt : &mut Cxt, givenedge : Edge, representation : &mut [usize], colour : &[usize]) {
    let mut startedge = [givenedge; MAXN + 1];
    let mut number = [0; MAXN];
    number[givenedge.start()] = 1;

    let mut last_number = 1;
    if givenedge.start() != givenedge.end() {
        number[givenedge.end()] = 2;
        last_number = 2;
        startedge[1] = givenedge.invers();
    }

    let mut actual_number = 1;
    let mut temp = givenedge;
    let mut rep_id = 0;

    while last_number < cxt.nv {
        let mut run = temp.next();
        while run != temp {
            let vertex = run.end();
            if number[vertex] == 0 {
                startedge[last_number] = run.invers();
                last_number += 1;
                number[vertex] = last_number;
                representation[rep_id] = colour[vertex]; // TODO: why???
            } else {
                representation[rep_id] = number[vertex];
            }
            rep_id += 1;

            run = run.next();
        }

        representation[rep_id] = 0;
        rep_id += 1;

        temp = startedge[actual_number];
        actual_number += 1;
    }

    while actual_number <= cxt.nv {
        let mut run = temp.next();
        while run != temp {
            representation[rep_id] = number[run.end()];
            rep_id += 1;

            run = run.next();
        }

        representation[rep_id] = 0;
        rep_id += 1;

        temp = startedge[actual_number];
        actual_number += 1;
    }
}


// Tests whether starting from a given edge and constructing the code in
// "->next" direction, an automorphism or even a better representation can
// be found. A better representation will be completely constructed and
// returned in "representation".  It works pretty similar to testcanon except
// for obviously necessary changes, so for extensive comments see testcanon
fn testcanon_init(cxt : &mut Cxt, givenedge : Edge, representation : &mut [usize], colour : &[usize]) -> i32 {
    let mut startedge = [givenedge; MAXN + 1];
    let mut number = [0; MAXN];
    number[givenedge.start()] = 1;

    let mut last_number = 1;
    if givenedge.start() != givenedge.end() {
        number[givenedge.end()] = 2;
        last_number = 2;
        startedge[1] = givenedge.invers();
    }

    let mut actual_number = 1;
    let mut temp = givenedge;
    let mut better = false;
    let mut rep_id = 0;

    while last_number < cxt.nv {
        let mut run = temp.next();
        while run != temp {
            let mut vertex = run.end();
            if number[vertex] == 0 {
                startedge[last_number] = run.invers();
                last_number += 1;
                number[vertex] = last_number;
                vertex = colour[vertex];
            } else { vertex = number[vertex]; }

            if better {
                representation[rep_id] = vertex;
            }  else {
                if vertex > representation[rep_id] {
                    return 0;
                } else if vertex < representation[rep_id] {
                    better = true;
                    representation[rep_id] = vertex;
                }
            }
            rep_id += 1;

            run = run.next();
        }

        if representation[rep_id] != 0 {
            better = true;
            representation[rep_id] = 0;
        }
        rep_id += 1;

        temp = startedge[actual_number];
        actual_number += 1;
    }

    while actual_number <= cxt.nv {
        let mut run = temp.next();
        while run != temp {
            let vertex = number[run.end()];

            if better {
                representation[rep_id] = vertex;
            } else {
                if vertex > representation[rep_id] {
                    return 0;
                } else if vertex < representation[rep_id] {
                    better = true;
                    representation[rep_id] = vertex;
                }
            }
            rep_id += 1;

            run = run.next();
        }

        if representation[rep_id] != 0 {
            better = true;
            representation[rep_id] = 0;
        }
        rep_id += 1;

        temp = startedge[actual_number];
        actual_number += 1;
    }

    if better { 2 } else { 1 }
}


// Tests whether starting from a given edge and constructing the code in
// "->prev" direction, an automorphism or even a better representation can
// be found. A better representation will be completely constructed and
// returned in "representation".  It works pretty similar to testcanon except
// for obviously necessary changes, so for extensive comments see testcanon
fn testcanon_mirror_init(cxt : &mut Cxt, givenedge : Edge, representation : &mut [usize], colour : &[usize]) -> i32 {
    let mut startedge = [givenedge; MAXN + 1];
    let mut number = [0; MAXN];
    number[givenedge.start()] = 1;

    let mut last_number = 1;
    if givenedge.start() != givenedge.end() {
        number[givenedge.end()] = 2;
        last_number = 2;
        startedge[1] = givenedge.invers();
    }

    let mut actual_number = 1;
    let mut temp = givenedge;
    let mut better = false;
    let mut rep_id = 0;

    while last_number < cxt.nv {
        let mut run = temp.prev();
        while run != temp {
            let mut vertex = run.end();
            if number[vertex] == 0 {
                startedge[last_number] = run.invers();
                last_number += 1;
                number[vertex] = last_number;
                vertex = colour[vertex];
            } else { vertex = number[vertex]; }

            if better {
                representation[rep_id] = vertex;
            } else {
                if vertex > representation[rep_id] {
                    return 0;
                } else if vertex < representation[rep_id] {
                    better = true;
                    representation[rep_id] = vertex;
                }
            }
            rep_id += 1;

            run = run.prev();
        }

        if representation[rep_id] != 0 {
            better = true;
            representation[rep_id] = 0;
        }
        rep_id += 1;

        temp = startedge[actual_number];
        actual_number += 1;
    }

    while actual_number <= cxt.nv {
        let mut run = temp.prev();
        while run != temp {
            let vertex = number[run.end()];
            if better {
                representation[rep_id] = vertex;
            } else {
                if vertex > representation[rep_id] {
                    return 0;
                } else if vertex < representation[rep_id] {
                    better = true;
                    representation[rep_id] = vertex;
                }
            }
            rep_id += 1;

            run = run.prev();
        }

        if representation[rep_id] != 0 {
            better = true;
            representation[rep_id] = 0;
        }
        rep_id += 1;

        temp = startedge[actual_number];
        actual_number += 1;
    }

    if better { 2 } else { 1 }
}


// Starts at givenedge and writes the edges in the well defined order
// into the list.  Works like testcanon. Look there for comments.
fn construct_numb(cxt : &mut Cxt, givenedge : Edge, numbering : &mut [Edge]) {
    let mut tail = 0;
    let limit = cxt.ne - 1;

    let mut startedge = [givenedge; MAXN + 1];
    let mut mark = [false; MAXN];
    mark[givenedge.start()] = true;

    let mut last_number = 1;
    if givenedge.start() != givenedge.end() {
        mark[givenedge.end()] = true;
        last_number = 2;
        startedge[1] = givenedge.invers();
    }

    let mut actual_number = 1;
    numbering[0] = givenedge;
    let mut temp = givenedge;

    while last_number < cxt.nv {
        let mut run = temp.next();
        while run != temp {
            let vertex = run.end();
            if !mark[vertex] {
                startedge[last_number] = run.invers();
                last_number += 1;
                mark[vertex] = true;
            }

            tail += 1;
            numbering[tail] = run;

            run = run.next();
        }

        if tail != limit {
            tail += 1;
            temp = startedge[actual_number];
            numbering[tail] = temp;
            actual_number += 1;
        }
    }

    // Now we know that all numbers have been given
    while tail != limit {
        let mut run = temp.next();
        while run != temp {
            tail += 1;
            numbering[tail] = run;

            run = run.next();
        }

        if tail != limit {
            tail += 1;
            temp = startedge[actual_number];
            numbering[tail] = temp;
            actual_number += 1;
        }
    }
}


// Starts at givenedge and writes the edges in the well defined order
// into the list.  Works like testcanon. Look there for comments.
fn construct_numb_mirror(cxt : &mut Cxt, givenedge : Edge, numbering : &mut [Edge]) {
    let mut tail = 0;
    let limit = cxt.ne - 1;

    let mut startedge = [givenedge; MAXN + 1];
    let mut mark = [false; MAXN];
    mark[givenedge.start()] = true;

    let mut last_number = 1;
    if givenedge.start() != givenedge.end() {
        mark[givenedge.end()] = true;
        last_number = 2;
        startedge[1] = givenedge.invers();
    }

    let mut actual_number = 1;
    numbering[0] = givenedge;
    let mut temp = givenedge;

    while last_number < cxt.nv {
        let mut run = temp.prev();
        while run != temp {
            let vertex = run.end();
            if !mark[vertex] {
                startedge[last_number] = run.invers();
                last_number += 1;
                mark[vertex] = true;
            }

            tail += 1;
            numbering[tail] = run;

            run = run.prev();
        }

        if tail != limit {
            tail += 1;
            temp = startedge[actual_number];
            numbering[tail] = temp;
            actual_number += 1;
        }
    }

    while tail != limit {
        let mut run = temp.prev();
        while run != temp {
            tail += 1;
            numbering[tail] = run;

            run = run.prev();
        }

        if tail != limit {
            tail += 1;
            temp = startedge[actual_number];
            numbering[tail] = temp;
            actual_number += 1;
        }
    }
}




// Checks whether the last vertex (number: nv-1) is canonical or not.
//   Returns 1 if yes, 0 if not. One of the criterions a canonical vertex
//   must fulfill is that its colour is minimal.
//
//   IT IS ASSUMED that the values of the colour function are positive
//   and at most INT_MAX-MAXN.
//
//   A possible starting edge for the construction of a representation is
//   one with lexicographically minimal colour pair (start,INT_MAX-end).
//   In can_numberings[][] the canonical numberings are stored as sequences
//   of oriented edges.  For every 0 <= i,j < *nbtot and every
//   0 <= k < ne the edges can_numberings[i][k] and can_numberings[j][k] can
//   be mapped onto each other by an automorphism. The first
//   *nbop numberings are orientation preserving while
//   the rest is orientation reversing.
//
//   In case of only 1 automorphism, in can_numberings[0][0] the "canonical"
//   edge is given.  It is one edge emanating at the canonical vertex. The
//   rest of the numbering is not given.
//
//   In case of nontrivial automorphisms, can[0] starts with a list of edges
//   adjacent to nv-1. In case of an orientation preserving numbering the deges
//   are listed in ->next direction, otherwise in ->prev direction.
//
//   Works OK if at least one vertex has valence >= 3. Otherwise some numberings
//   are computed twice, since changing the orientation (the cyclic order around
//   each vertex) doesn't change anything
pub fn canon(cxt : &mut Cxt, lcolour : &[usize], can_numberings : &mut [[Edge; MAXE]], nbtot : &mut usize, nbop : &mut usize) -> bool {
    let mut colour = [0; MAXN];
    for i in 0 .. cxt.nv {
        colour[i] = lcolour[i] + MAXN; // to distinguish colours from vertices
    }

    let last_vertex = cxt.nv - 1;
    let minstart = colour[last_vertex]; // (minstart,maxend) will be the chosen colour pair of an edge

    // determine the smallest possible end for the vertex "last_vertex"
    let end = cxt.firstedge[last_vertex];
    let mut maxend = colour[end.end()];
    let mut list_length_last = 1;
    let mut startlist_last = [end; 5];

    {
        let mut run = end.next();
        while run != end {
            if colour[run.end()] > maxend {
                startlist_last[0] = run;
                list_length_last = 1;
                maxend = colour[run.end()];
            } else if colour[run.end()] == maxend {
                startlist_last[list_length_last] = run;
                list_length_last += 1;
            }

            run = run.next();
        }
    }

    // Now we know the pair that SHOULD be minimal and we can determine a list
    // of all edges with this colour pair. If a new pair is found that is even
    // smaller, we can return 0 at once

    let mut startlist = [end; 5 * MAXN];
    let mut list_length = 0;
    for i in 0 .. last_vertex {
        if colour[i] < minstart { return false; }
        if colour[i] == minstart {
            let end = cxt.firstedge[i];
            let mut run = end;
            loop {
                if colour[run.end()] > maxend { return false; }
                if colour[run.end()] == maxend { startlist[list_length] = run; list_length += 1; }
                run = run.next();
                if run == end { break; }
            }
        }
    }

    // OK -- so there is no smaller pair and now we have to determine the
    // smallest representation around vertex "last_vertex":

    let mut representation = [0; MAXE];
    testcanon_first_init(cxt, startlist_last[0], &mut representation, &colour);

    // lists of edges where starting gives a canonical representation
    let mut numblist = [end; MAXE];
    let mut numblist_mirror = [end; MAXE];
    let mut numbs = 1;
    let mut numbs_mirror = 0;

    numblist[0] = startlist_last[0];
    match testcanon_mirror_init(cxt, startlist_last[0], &mut representation, &colour) {
        1 => {
            numbs_mirror = 1;
            numblist_mirror[0] = startlist_last[0];
        }
        2 => {
            numbs_mirror = 1;
            numbs = 0;
            numblist_mirror[0] = startlist_last[0];
        }
        _ => {}
    }

    for i in 1 .. list_length_last {
        match testcanon_init(cxt, startlist_last[i], &mut representation, &colour) {
            1 => { numblist[numbs] = startlist_last[i]; numbs += 1; }
            2 => { numbs_mirror = 0; numbs = 1; numblist[0] = startlist_last[i]; }
            _ => {}
        }

        match testcanon_mirror_init(cxt, startlist_last[i], &mut representation, &colour) {
            1 => { numblist_mirror[numbs_mirror] = startlist_last[i]; numbs_mirror += 1; }
            2 => { numbs_mirror = 1; numbs = 0; numblist_mirror[0] = startlist_last[i]; }
            _ => {}
        }
    }

    // Now we know the best representation we can obtain starting at last_vertex.
    // Now we will check all the others. We can return 0 at once if we find a
    // better one

    for i in 0 .. list_length {
        match testcanon(cxt, startlist[i], &representation, &colour) {
            1 => { numblist[numbs] = startlist[i]; numbs += 1; }
            2 => { return false; }
            _ => {}
        }

        match testcanon_mirror(cxt, startlist[i], &representation, &colour) {
            1 => { numblist_mirror[numbs_mirror] = startlist[i]; numbs_mirror += 1; }
            2 => { return false; }
            _ => {}
        }
    }


    *nbop = numbs;
    *nbtot = numbs + numbs_mirror;

    if numbs + numbs_mirror > 1 {
        for i in 0 .. numbs {
            construct_numb(cxt, numblist[i], &mut can_numberings[i]);
        }
        for i in 0 .. numbs_mirror {
            construct_numb_mirror(cxt, numblist_mirror[i], &mut can_numberings[numbs + i]);
        }
    } else {
        if numbs != 0 { can_numberings[0][0] = numblist[0]; }
        else { can_numberings[0][0] = numblist_mirror[0]; }
    }

    true
}


//   IT IS ASSUMED that the values of the colour function are positive
//   and at most INT_MAX-MAXN.
//
//   This routine checks all num_edges_or elements of edgelist_or just for one
//   orientation and all num_edges_inv elements of the list edgelist_inv just
//   for the other. It returns 1 if and only if one of the first can_edges_or
//   elements of the first list or first can_edges_inv elements of the second
//   give an optimal numbering among all the possibilities provided by the
//   lists.
//
//   Edges given are not in minimal form -- but it is guaranteed that all
//   colours of the startpoints are the same and all colours of the endpoints
//   are the same.
//
//   In case of only the identity automorphism, the entries of can_numberings[][]
//   are undefined.
//
//   Otherwise in can_numberings[][] the canonical numberings are stored as
//   sequences of oriented edges.  For every 0 <= i,j < *nbtot
//   and every 0 <= k < ne the edges can_numberings[i][k] and
//   can_numberings[j][k] can be mapped onto each other by an automorphism.
//   The first *nbop numberings are orientation
//   preserving while the rest are orientation reversing.
//
//   In case of an orientation preserving numbering the edges are listed in
//   ->next direction, otherwise in ->prev direction.
//
//   Works OK if at least one vertex has valence >= 3. Otherwise some numberings
//   are computed twice, since changing the orientation (the cyclic order around
//   each vertex) doesn't change anything
fn canon_edge_oriented(edgelist_or : &[Edge], num_edges_or : usize, can_edges_or : usize, edgelist_inv : &[Edge], num_edges_inv : usize, can_edges_inv : usize, lcolour : &[usize], can_numberings : &[[Edge; MAXE]], nbtot : &mut usize, nbop : &mut usize) -> bool {
    false

    //int i, test;
    //int representation[MAXE];
    //EDGE *numblist[MAXE], *numblist_mirror[MAXE]; /* lists of edges where
    //                            starting gives a canonical representation */
    //int numbs = 1, numbs_mirror = 0;
    //int colour[MAXN];
    //
    //for (i=0; i<nv; i++) colour[i]=lcolour[i]+MAXN;
    // to distinguish colours from vertices
    //
    // First we have to determine the smallest representation possible with
    //   edgelist_or
    //
    //if (can_edges_or > 0)
    //{ testcanon_first_init(edgelist_or[0], representation, colour);
    //numblist[0] = edgelist_or[0];
    //for (i=1; i<can_edges_or; i++)
    //{ test = testcanon_init(edgelist_or[i], representation, colour);
    //if (test == 1) { numblist[numbs] = edgelist_or[i]; numbs++; }
    //else if (test == 2)
    //{ numbs = 1; numblist[0] = edgelist_or[i]; }
    //}
    //i=0; /* the next for-loop can start at the beginning */
    //}
    //else
    //{ numbs=0; numbs_mirror=1;
    //testcanon_first_init_mirror(edgelist_inv[0], representation, colour);
    //numblist_mirror[0] = edgelist_inv[0];
    //i=1; /* the next for-loop must start at position 1 */
    //}
    //
    //for (   ; i<can_edges_inv; i++)
    //{ test = testcanon_mirror_init(edgelist_inv[i], representation, colour);
    //if (test == 1)
    //{ numblist_mirror[numbs_mirror] = edgelist_inv[i]; numbs_mirror++; }
    //else if (test == 2)
    //{ numbs = 0; numbs_mirror=1; numblist_mirror[0] = edgelist_inv[i]; }
    //}
    //
    //
    // now we know the best we can get for a "canonical edge".
    // Next we will check all the others. We can return 0 at once if we find a
    // better one
    //
    //for (i=can_edges_or ; i < num_edges_or; i++)
    //{ test = testcanon(edgelist_or[i], representation, colour);
    //if (test == 1) { numblist[numbs] = edgelist_or[i]; numbs++; }
    //else if (test == 2) return 0;
    //}
    //for (i=can_edges_inv ; i < num_edges_inv; i++)
    //{ test = testcanon_mirror(edgelist_inv[i], representation, colour);
    //if (test == 1)
    //{ numblist_mirror[numbs_mirror] = edgelist_inv[i]; numbs_mirror++; }
    //else if (test == 2) return 0;
    //}
    //
    //*nbop = numbs;
    //*nbtot = numbs+numbs_mirror;
    //
    //if (*nbtot > 1)
    //{
    //for (i = 0; i < numbs; i++)
    //construct_numb(numblist[i], can_numberings[i]);
    //for (i = 0; i < numbs_mirror; i++, numbs++)
    //construct_numb_mirror(numblist_mirror[i],can_numberings[numbs]);
    //}
    //
    //return 1;
}






// Determine the inequivalent places to make extensions, for general
// quadrangulations.  The results are put in the arrays
// extP0[0..*nextP0-1] and extP1[0..*nextP1-1].
// nbtot and nbop are the usual group parameters.
//static void find_extensions_quad_all(int nbtot, int nbop, EDGE *extP0[], int *nextP0, EDGE *extP1[], int *nextP1) {
    //EDGE *e,*elast;
    //EDGE **nb,**nb0,**nblim,**nboplim;
    //int i,j,k,l,x,y;
    //int deg2;
    //#define VCOLP0(i,j) (degree[i]<degree[j] ? \
    //(degree[j]<<10)+degree[i] : (degree[i]<<10)+degree[j])
    //
    //if (degree[nv-1] == 2)
    //{
    //x = firstedge[nv-1]->end;
    //y = firstedge[nv-1]->next->end;
    //}
    //else
    //x = -1;
    //
    //deg2 = 0;
    //for (i = nv; --i >= 0 && deg2 < 3;)
    //if (degree[i] == 2) ++deg2;
    //
    //if (nbtot == 1)
    //{
    // /* P0 extension for trivial group */
    //
    //RESETMARKS;
    //k = 0;
    //for (l = 0; l < nv; ++l)
    //{
    //e = elast = firstedge[l];
    //do
    //{
    //if (!ISMARKEDLO(e))
    //{
    //i = e->end;
    //j = e->next->end;
    //if (x < 0 || i == nv-1 || j == nv-1)
    //extP0[k++] = e;
    //else
    //{
    //++degree[i]; ++degree[j];
    //if (VCOLP0(i,j) >= VCOLP0(x,y)) extP0[k++] = e;
    //--degree[i]; --degree[j];
    //}
    //MARKLO(e->next->invers->next->invers);
    //}
    //e = e->next;
    //} while (e != elast);
    //}
    //
    //*nextP0 = k;
    //
    // /* P1 extension for trivial group */
    //
    //if (deg2 > 2)
    //*nextP1 = 0;
    //else
    //{
    //k = 0;
    //for (i = 0; i < nv; ++i)
    //if (degree[i] >= 4)
    //{
    //e = elast = firstedge[i];
    //do
    //{
    //if ((degree[e->prev->end]==2)
    //+(degree[e->next->end]==2) == deg2)
    //extP1[k++] = e;
    //e = e->next;
    //} while (e != elast);
    //}
    //
    //*nextP1 = k;
    //}
    //}
    //else
    //{
    //nboplim = (EDGE**)numbering[nbop==0?nbtot:nbop];
    //nblim = (EDGE**)numbering[nbtot];
    //nb0 = (EDGE**)numbering[0];
    //
    //for (i = 0; i < ne; ++i) nb0[i]->index = i;
    //
    // /* P0 extensions for non-trivial group */
    //
    //k = 0;
    //RESETMARKS;
    //
    //for (l = 0; l < ne; ++l)
    //if (!ISMARKED(nb0[l]))
    //{
    //e = nb0[l];
    //i = e->end;
    //j = e->next->end;
    //if (x < 0 || i == nv-1 || j == nv-1)
    //extP0[k++] = e;
    //else
    //{
    //++degree[i]; ++degree[j];
    //if (VCOLP0(i,j) >= VCOLP0(x,y)) extP0[k++] = e;
    //--degree[i]; --degree[j];
    //}
    //for (nb = nb0+l+MAXE; nb < nboplim; nb += MAXE)
    //MARKLO(*nb);
    //for ( ; nb < nblim; nb += MAXE)
    //MARKLO((*nb)->invers->next->invers);
    //for (nb = nb0+(nb0[l]->next->invers->next->invers->index);
    //nb < nboplim; nb += MAXE)
    //MARKLO(*nb);
    //for ( ; nb < nblim; nb += MAXE)
    //MARKLO((*nb)->invers->next->invers);
    //}
    //
    //*nextP0 = k;
    //
    // /* P1 extensions for non-trivial group */
    //
    //if (deg2 > 2)
    //*nextP1 = 0;
    //else
    //{
    //k = 0;
    //RESETMARKS;
    //
    //for (i = 0; i < nv; ++i)
    //if (degree[i] >= 4)
    //{
    //e = elast = firstedge[i];
    //do
    //{
    //if (!ISMARKEDLO(e))
    //{
    //if ((degree[e->prev->end]==2)
    //+(degree[e->next->end]==2) == deg2)
    //extP1[k++] = e;
    //for (nb = nb0+e->index+MAXE; nb < nblim; nb += MAXE)
    //MARKLO(*nb);
    //}
    //e = e->next;
    //} while (e != elast);
    //}
    //
    //*nextP1 = k;
    //}
    //}
//}




// The P0-operation with reference edge *ref has just been performed.
// Make a list in good_or[0..*ngood_or-1] of the reference edges of
// legal P1-reductions (oriented editions) that might be canonical,
// with the first *ngood_ref of those being ref.
// Make a list in good_mir[0..*ngood_mir-1] of the
// reference edges of legal four-reductions (mirror-image editions)
// that might be canonical, with the first *ngood_mir_ref of those being
// ref->next.
// *ngood_ref and *ngood_mir_ref might each be 0-1.  If they are
// both 0, nothing else need be correct.
// All the edges in good_or[] and good_mir[] must start with the same
// vertex degree and end with the same vertex degree (actually, colour
// as passed to canon_edge_oriented).
// P1-reductions have a priority (colour) based on the degrees of the
// end vertex and two side vertices.  It cannot be changed without
// changing find_extensions_quad too.
//
// version for general quadrangulations
//static void quadr_P0_legal_all(EDGE *ref, EDGE *good_or[], int *ngood_or, int *ngood_ref,  EDGE *good_mir[], int *ngood_mir, int *ngood_mir_ref) {
    //EDGE *e;
    //int col,col2,maxcol,maxcol2;
    //int i,nor,nmir;
    //int d1,d2,d3,d4;
    //
    //#define VCOLPD(di,dj) (di<dj ? (dj<<10)+di : (di<<10)+dj)
    //
    //nor = nmir = 0;
    //
    //d1 = degree[ref->end];
    //d2 = degree[ref->next->end];
    //d3 = degree[ref->invers->next->end];
    //d4 = degree[ref->invers->prev->end];
    //
    //maxcol = VCOLPD(d1,d2);
    //maxcol2 = VCOLPD(d3,d4);
    //
    //if (d1 >= d2)
    //{
    //if (d3 >= d4) good_or[nor++] = ref;
    //if (d4 >= d3) good_mir[nmir++] = ref;
    //}
    //if (d2 >= d1)
    //{
    //if (d4 >= d3) good_or[nor++] = ref->next;
    //if (d3 >= d4) good_mir[nmir++] = ref->next;
    //}
    //
    //*ngood_ref = nor;
    //*ngood_mir_ref = nmir;
    //
    //for (i = nv-1; --i >= 0; )
    //if (degree[i] == 2)
    //{
    //e = firstedge[i];
    //d1 = degree[e->end];
    //d2 = degree[e->next->end];
    //col = VCOLPD(d1,d2);
    //if (col > maxcol)
    //{
    //*ngood_ref = *ngood_mir_ref = 0;
    //return;
    //}
    //else if (col == maxcol)
    //{
    //d3 = degree[e->invers->next->end];
    //d4 = degree[e->invers->prev->end];
    //col2 = VCOLPD(d3,d4);
    //
    //if (col2 > maxcol2)
    //{
    //*ngood_ref = *ngood_mir_ref = 0;
    //return;
    //}
    //else if (col2 == maxcol2)
    //{
    //if (d1 >= d2)
    //{
    //if (d3 >= d4) good_or[nor++] = e;
    //if (d4 >= d3) good_mir[nmir++] = e;
    //}
    //if (d2 >= d1)
    //{
    //if (d4 >= d3) good_or[nor++] = e->next;
    //if (d3 >= d4) good_mir[nmir++] = e->next;
    //}
    //}
    //}
    //}
    //
    //if (nor > *ngood_ref || nmir > *ngood_mir_ref)
    //prune_oriented_lists(good_or,&nor,ngood_ref,
    //good_mir,&nmir,ngood_mir_ref);
    //
    //*ngood_or = nor;
    //*ngood_mir = nmir;
//}




// The P1-operation with reference edge *ref has just been performed.
// Make a list in good_or[0..*ngood_or-1] of the reference edges of
// legal P1-reductions (oriented editions) that might be canonical,
// with the first *ngood_ref of those being ref.
// Make a list in good_mir[0..*ngood_mir-1] of the
// reference edges of legal four-reductions (mirror-image editions)
// that might be canonical, with the first *ngood_mir_ref of those being
// ref->next.
// *ngood_ref and *ngood_mir_ref might each be 0-1.  If they are
// both 0, nothing else need be correct.
// All the edges in good_or[] and good_mir[] must start with the same
// vertex degree and end with the same vertex degree (actually, colour
// as passed to canon_edge_oriented).
// P1-reductions have a priority (colour) based on the degrees of the
// end vertex and two side vertices.  It cannot be changed without
// changing find_extensions_quad too.
//
// version for general quadrangulations
// assumes no vertices of degree 2
//static void quadr_P1_legal_all(EDGE *ref, EDGE *good_or[], int *ngood_or, int *ngood_ref, EDGE *good_mir[], int *ngood_mir, int *ngood_mir_ref) {
    //EDGE *e,*ee,*elast;
    //int maxdeg;
    //int col,maxcol;
    //int i,nor,nmir;
    //
    //#define QORCOL(e) (((long)degree[e->prev->end]<<10)+(long)degree[e->next->end])
    //#define QMIRCOL(e) (((long)degree[e->next->end]<<10)+(long)degree[e->prev->end])
    //
    //RESETMARKS;
    //nor = nmir = 0;
    //
    //maxdeg = degree[ref->end];
    //maxcol = QORCOL(ref);
    //col = QMIRCOL(ref);
    //if (col < maxcol)
    //good_or[nor++] = ref;
    //else if (col == maxcol)
    //{
    //good_or[nor++] = ref;
    //good_mir[nmir++] = ref;
    //}
    //else
    //{
    //maxcol = col;
    //good_mir[nmir++] = ref;
    //}
    //
    //*ngood_ref = nor;
    //*ngood_mir_ref = nmir;
    //
    //MARKLO(ref->invers);
    //
    //if (nor > *ngood_ref || nmir > *ngood_mir_ref)
    //prune_oriented_lists(good_or,&nor,ngood_ref,
    //good_mir,&nmir,ngood_mir_ref);
    //
    //if (*ngood_ref == 0 && *ngood_mir_ref == 0) return;
    //
    //for (i = 0; i < nv; ++i)
    //if (degree[i] > maxdeg)
    //{
    //e = elast = firstedge[i];
    //do
    //{
    //if (!ISMARKEDLO(e) && degree[e->end] == 3)
    //{
    //ee = e->invers;
    //if (legal_P1_reduction_all(ee))
    //{
    //*ngood_ref = *ngood_mir_ref = 0;
    //return;
    //}
    //}
    //e = e->next;
    //} while (e != elast);
    //}
    //else if (degree[i] == maxdeg)
    //{
    //e = elast = firstedge[i];
    //do
    //{
    //ee = e->invers;
    //if (degree[e->end] == 3 && !ISMARKEDLO(e)
    //&& legal_P1_reduction_all(ee))
    //{
    //col = QORCOL(e->invers);
    //if (col > maxcol)
    //{
    //*ngood_ref = *ngood_mir_ref = 0;
    //return;
    //}
    //else if (col == maxcol)
    //good_or[nor++] = e->invers;
    //
    //col = QMIRCOL(e->invers);
    //if (col > maxcol)
    //{
    //*ngood_ref = *ngood_mir_ref = 0;
    //return;
    //}
    //else if (col == maxcol)
    //good_mir[nmir++] = e->invers;
    //}
    //e = e->next;
    //} while (e != elast);
    //}
    //
    //if (nor > *ngood_ref || nmir > *ngood_mir_ref)
    //prune_oriented_lists(good_or,&nor,ngood_ref,
    //good_mir,&nmir,ngood_mir_ref);
    //
    //*ngood_or = nor;
    //*ngood_mir = nmir;
//}



// Test whether there is a legal P1 reduction
fn has_quadr_P0(cxt : &Cxt) -> bool {
    for i in 0 .. cxt.nv {
        if cxt.degree[i] == 2 {
            return true;
        }
    }

    false
}



// extends a graph in the way given by the type P0 extension for
// quadrangulations.
//
// The new path is inserted on the left of e1.
//
// It returns the directed edge starting at the new vertex with the
// new face on its left.
//
// In the picture: e1=b->a, the edge c->a is returned and
// vertex c is the new point nv.
//
//     ?
//     a
//    / \
//  ?b   c?
//    \ /
//     d
//     ?
//fn extend_quadr_P0(e1 : Edge) -> Edge {
//    register EDGE *start, *dummy, *dummy2;
//    int buffer;
//
//    start=quadr_P0(nv);
//
//    degree[nv]=2;
//
//    buffer=e1->end;
//    dummy=e1->invers; dummy2=dummy->prev;
//    start->start=buffer;
//    start->next=dummy; dummy->prev=start;
//    start->prev=dummy2; dummy2->next=start;
//    degree[buffer]++;
//
//    start++;
//    firstedge[nv]=start;
//    start->end=buffer;
//
//    e1=e1->next;
//    start++;
//    buffer=e1->end;
//    dummy=e1->invers; dummy2=dummy->next;
//    start->start=buffer;
//    start->next=dummy2; dummy2->prev=start;
//    start->prev=dummy; dummy->next=start;
//    degree[buffer]++;
//
//    (start+1)->end=buffer;
//
//    nv++; ne+=4;
//
//    return (start-1);
//}


// reduces a graph previously extended by the P0 extension for
// quadrangulations. The edge e must be the reference edge
// returned by the expansion routine.
fn reduce_quadr_P0(cxt : &mut Cxt, e : Edge) {
    //register EDGE *dummy, *dummy2;
    //int buffer;

    cxt.nv -= 1;
    cxt.ne -= 4;

    let mut dummy = e.invers();
    let mut dummy2 = dummy.next();
    dummy = dummy.prev();

    //dummy->next = dummy2; dummy2->prev=dummy;
    let mut buffer = dummy.start();
    cxt.firstedge[buffer] = dummy;
    cxt.degree[buffer] -= 1;

    //dummy=e->prev->invers;
    //dummy2=dummy->next;
    //dummy=dummy->prev;

    //dummy->next=dummy2; dummy2->prev=dummy;
    //buffer=dummy->start;
    //firstedge[buffer]=dummy; degree[buffer]--;
}



// The main node of the recursion for general simple quadrangulations.
// As this procedure is entered, nv,ne,degree etc are set for some graph,
// and nbtot/nbop are the values returned by canon() for that graph.
pub fn scanquadrangulations_all(cxt : &mut Cxt, nbtot : usize, nbop : usize) {
//EDGE *firstedge_save[MAXN];
//EDGE *extP0[MAXE],*extP1[MAXE];
//EDGE *good_or[MAXE],*good_mir[MAXE];
//int ngood_or,ngood_mir,ngood_ref,ngood_mir_ref;
//int nextP0,nextP1,i;
//int xnbtot,xnbop,conn;
//EDGE *rededge;

    if cxt.nv == cxt.maxnv {
//        if (pswitch || xswitch) conn = con_quad();
//        else                    conn = 2;           /* really 2 or 3 */
//
//        if (pswitch) startbipscan(nbtot,nbop,conn);
//        else         got_one(nbtot,nbop,conn);

        println!("Hello!");
        return;
    }

    if cxt.nv == cxt.splitlevel {
//        #ifdef SPLITTEST
//        ADDBIG(splitcases,1);
//        return;
//        #endif
//        if (splitcount-- != 0) return;
//        splitcount = mod - 1;
//
//        for (i = 0; i < nv; ++i) firstedge_save[i] = firstedge[i];
    }

//#ifdef PRE_FILTER_QUAD_ALL
//if (!(PRE_FILTER_QUAD_ALL)) return;
//#endif


    //EDGE *extP0[MAXE],*extP1[MAXE];
    //int nextP0,nextP1,i;
    let nextP0 = 0;
    let nextP1 = 0;
    //find_extensions_quad_all(nbtot, nbop, extP0, &nextP0, extP1, &nextP1);

    for i in 0 .. nextP0 {
        //let rededge = extend_quadr_P0(extP0[i]);

//#ifdef FAST_FILTER_QUAD_ALL
//if (FAST_FILTER_QUAD_ALL)
//#endif

        {
            //EDGE *good_or[Edge; MAXE],*good_mir[MAXE];
            let mut ngood_or = 0;
            let mut ngood_ref = 0;
            let mut ngood_mir = 0;
            let mut ngood_mir_ref = 0;
            //quadr_P0_legal_all(rededge, good_or, &ngood_or, &ngood_ref, good_mir, &ngood_mir, &ngood_mir_ref);

            if ngood_ref + ngood_mir_ref > 0 {
                if cxt.nv == cxt.maxnv && !needgroup && ngood_or == ngood_ref && ngood_mir == ngood_mir_ref {
                    //got_one(1, 1, 2);
                } else if ngood_or + ngood_mir == 1 {
                    scanquadrangulations_all(cxt, 1, 1);
                } else {
                    let mut xnbtot = 0;
                    let mut xnbop = 0;
                    if canon_edge_oriented(good_or, ngood_or, ngood_ref, good_mir, ngood_mir, ngood_mir_ref, &cxt.degree, numbering, &mut xnbtot, &mut xnbop) {
                        scanquadrangulations_all(cxt, xnbtot, xnbop);
                    }
                }
            }
        }

        //reduce_quadr_P0(rededge);
    }

    for i in 0 .. nextP1 {
        //rededge = extend_quadr_P1(extP1[i]);
//#ifdef FAST_FILTER_QUAD_ALL
//if (FAST_FILTER_QUAD_ALL)
//#endif

        //{
            //if (!has_quadr_P0()) {
                //quadr_P1_legal_all(rededge,good_or,&ngood_or,&ngood_ref,good_mir,&ngood_mir,&ngood_mir_ref);
                //if (ngood_ref+ngood_mir_ref > 0 && canon_edge_oriented(good_or,ngood_or,ngood_ref,good_mir,ngood_mir,ngood_mir_ref,degree,numbering,&xnbtot,&xnbop))
                    //scanquadrangulations_all(xnbtot,xnbop);
            //}
        //}

        // reduce_quadr_P1(rededge);
    }

    if cxt.nv == cxt.splitlevel {
        //for (i = 0; i < nv; ++i) firstedge[i] = firstedge_save[i];
    }
}
