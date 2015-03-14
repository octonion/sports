#include "stdafx.h" // for MS Visual C++ only

// C++ Program for Computing Kemeny-Young Combined Preferences
// William H. Press, University of Texas at Austin
// August, 2012

// Numerical Recipes files (from http://www.nr.com)
#include "nr3.h"
#include "sort.h"
#include "ran.h"
#include "hash.h"
#include "erf.h"
// other includes
#include <algorithm>
using namespace std;

#define SHOWINPUT 0 // nonzero includes input data in the output file
#define ALLSCORES 0 // nonzero uses all greedy minimizations, not just best
#define MPERM 7 // window size for exhaustively tried permutations
Int MAXVOTERS=3000, MAXCANDS=1000, MAXCANDNAMELEN=64, BUFFLEN=1024;
Ran ran(10990101); // random generator seed

Normaldist normaldist;

struct RanksFile  {
	MatChar thedata;
	Int nrankers, ncands, nprefs;
	Hash<char,Int,Hashfn2> names;
	MatChar unnames;
	MatDoub prefmat;

	RanksFile(FILE *infile, FILE *outfile, FILE *messages) : thedata(MAXVOTERS,BUFFLEN),
		nrankers(0), ncands(0), nprefs(0), names(MAXCANDS,MAXCANDS), unnames(MAXCANDS,MAXCANDNAMELEN) {
		int i,j,jcand, nvotes;
		char *cp;
		VecInt onevote(MAXCANDS);
		MatDoub tmpprefmat(MAXCANDS,MAXCANDS,0.);
		FILE *INP = infile;
		FILE *OUTP = outfile;
		FILE *MESS = messages;
		if (SHOWINPUT) fprintf(OUTP, "*** Using this input data: ***\n");
		while (fscanf(INP, "%[^\r\n]%*[\r\n]",&thedata[nrankers][0]) == 1) {
			nvotes = 0;
			onevote.assign(MAXCANDS,0);
			cp = &thedata[nrankers][0];
			if (SHOWINPUT) fprintf(OUTP,"%s\n",cp);
			cp = strtok(cp," \t");
			while (cp != NULL) { // read all votes on one line
				cp = strtok(NULL," \t");
				if (cp==NULL) break;
				if (names.get(cp[0],jcand) == 0) { // name not yet stored
					names.set(cp[0],ncands);
					strcpy(&unnames[ncands][0],cp);
					jcand = ncands;
					ncands++;
				}
				onevote[nvotes++] = jcand;
			}
			for (i=0;i<nvotes-1;i++) for (j=i+1;j<nvotes;j++) {
				tmpprefmat[onevote[i]][onevote[j]] += 1;
				tmpprefmat[onevote[j]][onevote[i]] -= 1;
				nprefs += 1;
			}
			nrankers++;
		}
		prefmat.resize(ncands,ncands);
		for (i=0;i<ncands;i++) for (j=0;j<ncands;j++) prefmat[i][j] = tmpprefmat[i][j];
		fprintf(MESS,"*** There are %d candidates and %d voters. ***\n",ncands,nrankers);
	}

};

struct KemenyYoung {
	Int np;
	Doub lastscore;
	MatDoub v; // v_ij is count of prefer i to j
	VecInt p;
	static const Int printflag = 0, mperm=MPERM;

	KemenyYoung(MatDoub &vv) : np(vv.nrows()), v(vv), p(np) {
		Int i;
		Doub oldscore,newscore;
		init();
		oldscore = lastscore = score();
		for (;;) {
			moveinsert();
			for (i=0;i<=np-mperm;i++) localpermute(i,i+mperm-1);
			newscore = score();
			if (printflag) printf("newscore = %g oldscore=%g\n",newscore,oldscore);
			if (newscore <= oldscore) break;
			oldscore = newscore;
		}
		lastscore = score();
	}

	Doub score() { // score the permutation
		Int i,j;
		Doub ans = 0.;
		for (i=0;i<np-1;i++) for (j=i+1;j<np;j++) {
			ans += (v[p[i]][p[j]] - v[p[j]][p[i]]);
		}
		if (printflag) printf("score = %g\n",ans);
		return ans;
	}

	Doub score(Int lo, Int hi) { // score a subrange
		Int i,j;
		Doub ans = 0.;
		for (i=lo;i<hi;i++) for (j=i+1;j<=hi;j++) {
			ans += (v[p[i]][p[j]] - v[p[j]][p[i]]);
		}
		//if (printflag) printf("iscore = %g\n",ans);
		return ans;
	}

	void moveinsert() {
		Int i,ii,j,jj,pp;
		VecDoub dscore(np);
		VecInt to(np);
		Doub ds;
		VecInt perm(np);
		for (i=0;i<np;i++) perm[i] = i;
		for (i=0;i<np-1;i++) {
			j = i + (ran.int32() % (np-i));
			if (j > np-1) throw("bad perm");
			SWAP(perm[i],perm[j]);
		}
		for (ii=0;ii<np;ii++) { // try to move i
			i = perm[ii];
			dscore[i] = 0.;
			ds = 0.;
			for (j=i-1;j>=0;j--) { // move up to before j
				ds += 2.*(v[p[i]][p[j]]-v[p[j]][p[i]]);
				dscore[j] = ds;
			}
			ds = 0.;
			for (j=i+1;j<np;j++) { // move down to after j
				ds += 2.*(v[p[j]][p[i]]-v[p[i]][p[j]]);
				dscore[j] = ds;
			}
			ds = -1.e99; // find best move:
			for (j=0;j<np;j++) if (j != i) if (dscore[j] > ds) {
				ds = dscore[j];
				jj = j;
			}
			if (ds > 0.) { // do the move
				pp = p[i];
				if (jj < i) {
					for (j=i-1;j>=jj;j--) p[j+1] = p[j];
				} else { // jj > i
					for (j=i+1;j<=jj;j++) p[j-1] = p[j];
				}
				p[jj] = pp;
				lastscore += ds;
				if (printflag) printf("moving %d to %d, score should be %g\n",i,jj,lastscore);
			}
		}
	}

	void init() {
	// guess initial permutation by mean ranks
		Int i,k;
		VecDoub r(np);
		Doub sik, ski;
		for (i=0;i<np;i++) {
			sik = ran.doub(); // will break ties
			ski = ran.doub();
			for (k=0;k<np;k++) if (k != i) {
				sik += v[i][k];
				ski += v[k][i];
			}
			r[i] = ski/(ski+sik); // smaller value is better
		}
		Indexx ndx(r);
		for (i=0;i<np;i++) p[i] = ndx.indx[i]; // smallest i best
	}

	void localpermute(Int lo, Int hi) {
		Int i;
		Doub oldscore, hiscore, newscore;
		VecInt pbest(hi-lo+1), psav(hi-lo+1);
		oldscore = hiscore = score(lo,hi);
		for (i=lo;i<=hi;i++) psav[i-lo] = pbest[i-lo] = p[i];
		sort(&p[lo],&p[hi]+1); // STL library!
		do {    		
			newscore = score(lo,hi);
			if (newscore > hiscore) {
				hiscore = newscore;
				for (i=lo;i<=hi;i++) pbest[i-lo] = p[i];
			}
		} while (next_permutation(&p[lo],&p[hi]+1)); // STL library!
		if (hiscore > oldscore || (hiscore == oldscore && ran.doub() < 0.333)) {// somewhat randomize on equal case
			lastscore += (hiscore-oldscore);
			for (i=lo;i<=hi;i++) p[i] = pbest[i-lo];
			if (printflag) printf("perm better by %g, score s.b.%g\n",hiscore-oldscore,lastscore);
			if (printflag) score();
		} else {
			for (i=lo;i<=hi;i++) p[i] = psav[i-lo];
		}
	}

	VecDoub yscores() {
		Int i;
		VecDoub y(np);
		for (i=0;i<np;i++) {
			y[p[i]] = (np-i-0.5)/np;
		}
		return y;
	}

};

int main(int argc, char **argv) {
	Int i,ii,ntry,nbest=0,ntries=1;
	if (argc < 2) {printf("usage: kemenyyoung number_of_iterations < inputfile > outputfile\n"); exit(1);}
	else sscanf(argv[1],"%d",&ntries);
	FILE *INP=stdin, *OUTP=stdout, *MESS=stderr;
	if (! INP) {printf("*** bad input file name ***\n"); exit(1);}
	if (! OUTP) {printf("*** bad output file name ***\n"); exit(1);}
	if (! MESS) {printf("*** bad message file name ***\n"); exit(1);}
	RanksFile ranksfile(INP,OUTP,MESS);
	Int ncands = ranksfile.ncands;
	Doub bestscore=0.;
	VecInt rankmax(ncands,0), rankmin(ncands,ncands);
	VecDoub rankmean(ncands,0.), ranksig(ncands,0.);
	fprintf(MESS,"*** Please be patient, while I crunch...\n");
	for (ntry=0;ntry<ntries;ntry++) {
		KemenyYoung ky(ranksfile.prefmat);
		if (ky.lastscore > bestscore && ! ALLSCORES) { // throw out previous sub-optimal scores
			rankmax.assign(ncands,0);
			rankmin.assign(ncands,ncands+1);
			rankmean.assign(ncands,0.);
			ranksig.assign(ncands,0.);
			nbest = 0;
			bestscore = ky.lastscore;
		}
		if (ky.lastscore == bestscore || ALLSCORES) { // a tie for optimal, so keep it
			for (i=0;i<ncands;i++) {
				if (i > rankmax[ky.p[i]]) rankmax[ky.p[i]] = i;
				if (i < rankmin[ky.p[i]]) rankmin[ky.p[i]] = i;
				rankmean[ky.p[i]] += i;
				ranksig[ky.p[i]] += SQR(i);
			}
			++nbest;
		}
	}
	for (i=0;i<ncands;i++) rankmean[i] /= nbest;
	for (i=0;i<ncands;i++) ranksig[i] /= nbest;
	for (i=0;i<ncands;i++) ranksig[i] = sqrt(MAX(0.,ranksig[i] - SQR(rankmean[i])));
	fprintf(MESS,"*** Score: %.0f preferences out of %d are honored.\n",bestscore/2., ranksfile.nprefs);
	fprintf(MESS,"*** Now sending results to output file.\n");
	if (SHOWINPUT) fprintf(OUTP,"The results are:\n");
	fprintf(OUTP,"%6s candidate best worst average in %d tied orderings\n"," ",nbest);
	Indexx ndx(rankmean);
	for (ii=0;ii<ncands;ii++) {
		i = ndx.indx[ii];
		fprintf(OUTP,"%16s %4d %4d %8.3f +- %.3f\n",&ranksfile.unnames[i][0],rankmin[i]+1,rankmax[i]+1,
			rankmean[i]+1.,ranksig[i]);
	}
	return 0;
}
