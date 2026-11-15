/*
 * TTreeAu (tta) - a file manager for Linux in the style of XTreeGold
 *
 * Copyright (c) 1989-1993, 2026 Paul Khoury
 *
 * Written in plain C89 against ncurses so it builds on old systems
 * (Debian woody: gcc 2.95, glibc 2.2, ncurses 5.2) as well as new ones.
 *
 * Build:  gcc -O2 -o tta tta.c -lncurses
 */

#define _GNU_SOURCE
#define _FILE_OFFSET_BITS 64

#include <curses.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <stdarg.h>
#include <ctype.h>
#include <errno.h>
#include <time.h>
#include <unistd.h>
#include <fcntl.h>
#include <dirent.h>
#include <fnmatch.h>
#include <signal.h>
#include <termios.h>
#include <utime.h>
#include <ftw.h>
#include <locale.h>
#include <langinfo.h>
#include <pwd.h>
#include <grp.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/statvfs.h>
#include <sys/wait.h>

#define TTA_VERSION "3.01"
#define MAXP 4096
#define ALT(c) (0x2000 | (c))
#define CTL(c) ((c) & 0x1f)
#define K_F(n) (KEY_F0 + (n))

/* ------------------------------------------------------------------ */
/* data                                                                */
/* ------------------------------------------------------------------ */

typedef struct Dir Dir;

typedef struct FileEnt {
    char  *name;
    off_t  size;
    time_t mtime;
    mode_t mode;
    uid_t  uid;
    gid_t  gid;
    int    tagged;
    Dir   *dir;
} FileEnt;

struct Dir {
    char    *name;
    Dir     *parent;
    Dir    **kids;
    int      nkids;
    FileEnt *files;
    int      nfiles;
    int      logged, expanded, err, mark;
    dev_t    dev;
};

typedef struct {
    Dir      *cur;
    int       ttop;
    int       fmode;      /* 0 = tree window, 1 = file window         */
    int       lmode;      /* 0 = directory, 1 = branch, 2 = showall    */
    int       tagonly;
    FileEnt **fl;
    int       nfl, fcap, fsel, ftop;
    int       vrows, vcols;
    char      selname[256];
    Dir      *seldir;
} Pane;

static Dir  *root;
static Pane  P[2];
static int   npanes = 1, ap = 0;
static int   autoview = 0, fmtmode = 0, sortmode = 0;  /* fmtmode: 0 names, 1 +perms, 2 +size/date/perms */
static int   log_all_at_start = 1;  /* ~/.ttarc: log = all | lazy */
static int   lists_dirty = 1, stats_dirty = 1;
static int   W, H, RW = 22;
static int   show_about = 0;
static time_t about_until = 0;
static int   utf8 = 0;
static int   quit_flag = 0;
static int   clock24 = 1;      /* ~/.ttarc: clock=24 or clock=12 */
static char  quit_dir[MAXP] = "";

static char *specs[32];
static int   nspecs = 0;
static char  specstr[256] = "*";

static Dir **vis;
static int   nvis, cvis;

static struct {
    long dirs, files, mfiles, tfiles;
    long long bytes, mbytes, tbytes;
} ST;

static chtype AN, AH, AB, AD, AT, AE, AI;   /* normal hot bar dim title error inactive-bar */

static const char *sortnames[] = { "name", "extension", "size", "date" };

/* ------------------------------------------------------------------ */
/* utilities                                                           */
/* ------------------------------------------------------------------ */

static void die(const char *m)
{
    endwin();
    fprintf(stderr, "tta: %s\n", m);
    exit(1);
}

static void *xmalloc(size_t n)
{
    void *p = malloc(n ? n : 1);
    if (!p) die("out of memory");
    return p;
}

static void *xrealloc(void *o, size_t n)
{
    void *p = realloc(o, n ? n : 1);
    if (!p) die("out of memory");
    return p;
}

static char *xstrdup(const char *s)
{
    char *p = xmalloc(strlen(s) + 1);
    strcpy(p, s);
    return p;
}

static void scopy(char *d, const char *s, size_t n)
{
    if (!n) return;
    strncpy(d, s, n - 1);
    d[n - 1] = 0;
}

static int cmpstr(const char *a, const char *b)
{
    int r = strcasecmp(a, b);
    return r ? r : strcmp(a, b);
}

static void commas(long long v, char *out)
{
    char t[32];
    int n, i, j = 0;
    sprintf(t, "%lld", v);
    n = strlen(t);
    for (i = 0; i < n; i++) {
        int k = n - 1 - i;
        out[j++] = t[i];
        if (k > 0 && k % 3 == 0) out[j++] = ',';
    }
    out[j] = 0;
}

/* decimal units, so 496,592 -> 497K and 262,111,744 -> 262M */
static void human(double v, char *out)
{
    const char *u = " KMGTPE";
    int i = 0;
    while (v >= 999.5 && i < 6) { v /= 1000.0; i++; }
    if (i == 0) sprintf(out, "%.0f", v);
    else if (v < 9.95) sprintf(out, "%.1f%c", v, u[i]);
    else sprintf(out, "%.0f%c", v, u[i]);
}

/* comma form if it fits in width, otherwise abbreviated */
static void numfit(long long v, int width, char *out)
{
    commas(v, out);
    if ((int)strlen(out) > width) human((double)v, out);
}

static void join_path(char *out, size_t n, const char *dir, const char *name)
{
    if (!strcmp(dir, "/")) snprintf(out, n, "/%s", name);
    else snprintf(out, n, "%s/%s", dir, name);
}

static void dir_path(Dir *d, char *buf, size_t n)
{
    const char *parts[1024];
    int k = 0, i;
    size_t len = 0;
    Dir *x;
    if (!d->parent) { scopy(buf, "/", n); return; }
    for (x = d; x->parent && k < 1024; x = x->parent) parts[k++] = x->name;
    buf[0] = 0;
    for (i = k - 1; i >= 0; i--) {
        size_t l = strlen(parts[i]);
        if (len + l + 2 >= n) break;
        buf[len++] = '/';
        memcpy(buf + len, parts[i], l);
        len += l;
        buf[len] = 0;
    }
}

static void file_path(FileEnt *f, char *out, size_t n)
{
    char d[MAXP];
    dir_path(f->dir, d, sizeof d);
    join_path(out, n, d, f->name);
}

static const char *base_name(const char *p)
{
    const char *s = strrchr(p, '/');
    return s ? s + 1 : p;
}

/* shell-quote with single quotes */
static void shquote(const char *s, char *out, size_t n)
{
    size_t j = 0;
    if (n < 3) { if (n) out[0] = 0; return; }
    out[j++] = '\'';
    for (; *s && j + 5 < n; s++) {
        if (*s == '\'') { memcpy(out + j, "'\\''", 4); j += 4; }
        else out[j++] = *s;
    }
    out[j++] = '\'';
    out[j] = 0;
}

static void expand_path(const char *in, const char *base, char *out, size_t n)
{
    char tmp[MAXP];
    while (*in == ' ') in++;
    if (in[0] == '~' && (in[1] == '/' || in[1] == 0)) {
        const char *h = getenv("HOME");
        snprintf(tmp, sizeof tmp, "%s%s", h ? h : "", in + 1);
    } else if (in[0] == '/') {
        scopy(tmp, in, sizeof tmp);
    } else {
        join_path(tmp, sizeof tmp, base, in);
    }
    /* strip trailing slashes (but keep "/") */
    {
        size_t l = strlen(tmp);
        while (l > 1 && tmp[l - 1] == '/') tmp[--l] = 0;
    }
    scopy(out, tmp, n);
}

static void lsmode(mode_t m, char *b)
{
    b[0] = S_ISDIR(m) ? 'd' : S_ISLNK(m) ? 'l' : S_ISCHR(m) ? 'c' : S_ISBLK(m) ? 'b' :
           S_ISFIFO(m) ? 'p' : S_ISSOCK(m) ? 's' : '-';
    b[1] = (m & S_IRUSR) ? 'r' : '-';
    b[2] = (m & S_IWUSR) ? 'w' : '-';
    b[3] = (m & S_ISUID) ? ((m & S_IXUSR) ? 's' : 'S') : ((m & S_IXUSR) ? 'x' : '-');
    b[4] = (m & S_IRGRP) ? 'r' : '-';
    b[5] = (m & S_IWGRP) ? 'w' : '-';
    b[6] = (m & S_ISGID) ? ((m & S_IXGRP) ? 's' : 'S') : ((m & S_IXGRP) ? 'x' : '-');
    b[7] = (m & S_IROTH) ? 'r' : '-';
    b[8] = (m & S_IWOTH) ? 'w' : '-';
    b[9] = (m & S_ISVTX) ? ((m & S_IXOTH) ? 't' : 'T') : ((m & S_IXOTH) ? 'x' : '-');
    b[10] = 0;
}

static void fmt_date(time_t t, char *b)
{
    struct tm *tm = localtime(&t);
    int h;
    if (!tm) { strcpy(b, "--------  -:--:-- --"); return; }
    if (clock24) {
        sprintf(b, "%02d-%02d-%02d %02d:%02d:%02d", tm->tm_mon + 1, tm->tm_mday,
                tm->tm_year % 100, tm->tm_hour, tm->tm_min, tm->tm_sec);
        return;
    }
    h = tm->tm_hour % 12;
    if (!h) h = 12;
    sprintf(b, "%02d-%02d-%02d %2d:%02d:%02d %s", tm->tm_mon + 1, tm->tm_mday,
            tm->tm_year % 100, h, tm->tm_min, tm->tm_sec, tm->tm_hour < 12 ? "am" : "pm");
}

static void fmt_date_short(time_t t, char *b)
{
    struct tm *tm = localtime(&t);
    int h;
    if (!tm) { strcpy(b, "-------- --:--"); return; }
    if (clock24) {
        sprintf(b, "%02d-%02d-%02d %02d:%02d", tm->tm_mon + 1, tm->tm_mday,
                tm->tm_year % 100, tm->tm_hour, tm->tm_min);
        return;
    }
    h = tm->tm_hour % 12;
    if (!h) h = 12;
    sprintf(b, "%02d-%02d-%02d %2d:%02d%c", tm->tm_mon + 1, tm->tm_mday,
            tm->tm_year % 100, h, tm->tm_min, tm->tm_hour < 12 ? 'a' : 'p');
}

/* ------------------------------------------------------------------ */
/* system info                                                         */
/* ------------------------------------------------------------------ */

static long long free_memory(void)
{
    FILE *f = fopen("/proc/meminfo", "r");
    char line[256];
    long long avail = -1, mfree = 0, buf = 0, cached = 0, v;
    if (!f) return -1;
    while (fgets(line, sizeof line, f)) {
        if (sscanf(line, "MemAvailable: %lld", &v) == 1) avail = v;
        else if (sscanf(line, "MemFree: %lld", &v) == 1) mfree = v;
        else if (sscanf(line, "Buffers: %lld", &v) == 1) buf = v;
        else if (sscanf(line, "Cached: %lld", &v) == 1) cached = v;
    }
    fclose(f);
    if (avail < 0) avail = mfree + buf + cached;   /* 2.2 / 2.4 kernels */
    return avail * 1024;
}

static void unescape_mnt(char *s)
{
    char *r = s, *w = s;
    while (*r) {
        if (r[0] == '\\' && r[1] >= '0' && r[1] <= '7' && r[2] && r[3]) {
            *w++ = (char)(((r[1] - '0') << 6) | ((r[2] - '0') << 3) | (r[3] - '0'));
            r += 4;
        } else *w++ = *r++;
    }
    *w = 0;
}

static void mount_info(const char *path, char *dev, size_t dn, char *mnt, size_t mn,
                       char *type, size_t tn)
{
    FILE *f = fopen("/proc/mounts", "r");
    char line[1024], d[512], m[512], t[64];
    size_t best = 0;
    scopy(dev, "?", dn);
    scopy(mnt, "/", mn);
    scopy(type, "?", tn);
    if (!f) return;
    while (fgets(line, sizeof line, f)) {
        size_t l;
        if (sscanf(line, "%511s %511s %63s", d, m, t) != 3) continue;
        unescape_mnt(m);
        unescape_mnt(d);
        l = strlen(m);
        if (strncmp(path, m, l) != 0) continue;
        if (!(l == 1 || path[l] == 0 || path[l] == '/')) continue;
        if (l >= best) {
            best = l;
            scopy(dev, d, dn);
            scopy(mnt, m, mn);
            scopy(type, t, tn);
        }
    }
    fclose(f);
}

static struct {
    char path[MAXP];
    time_t when;
    char dev[256], mnt[MAXP], type[64];
    long long avail, total;
} DK;

static void update_disk(const char *path)
{
    struct statvfs sv;
    time_t now = time(NULL);
    if (!strcmp(path, DK.path) && now - DK.when < 3) return;
    scopy(DK.path, path, sizeof DK.path);
    DK.when = now;
    mount_info(path, DK.dev, sizeof DK.dev, DK.mnt, sizeof DK.mnt, DK.type, sizeof DK.type);
    if (statvfs(path, &sv) == 0) {
        DK.avail = (long long)sv.f_bavail * (long long)(sv.f_frsize ? sv.f_frsize : sv.f_bsize);
        DK.total = (long long)sv.f_blocks * (long long)(sv.f_frsize ? sv.f_frsize : sv.f_bsize);
    } else {
        DK.avail = DK.total = -1;
    }
}

/* ------------------------------------------------------------------ */
/* filespec                                                            */
/* ------------------------------------------------------------------ */

static void set_specs(const char *s)
{
    char buf[256], *tok;
    int i;
    for (i = 0; i < nspecs; i++) free(specs[i]);
    nspecs = 0;
    scopy(buf, s, sizeof buf);
    for (tok = strtok(buf, " ,;\t"); tok && nspecs < 32; tok = strtok(NULL, " ,;\t")) {
        if (!strcmp(tok, "*.*")) tok = "*";
        specs[nspecs++] = xstrdup(tok);
    }
    if (!nspecs) specs[nspecs++] = xstrdup("*");
    specstr[0] = 0;
    for (i = 0; i < nspecs; i++) {
        if (i) strncat(specstr, " ", sizeof specstr - strlen(specstr) - 1);
        strncat(specstr, specs[i], sizeof specstr - strlen(specstr) - 1);
    }
}

static int matches(const char *n)
{
    int i, any = 0, ok = 0;
    for (i = 0; i < nspecs; i++) {
        const char *p = specs[i];
        if (p[0] == '-' && p[1]) {
            if (fnmatch(p + 1, n, 0) == 0) return 0;
        } else {
            any = 1;
            if (fnmatch(p, n, 0) == 0) ok = 1;
        }
    }
    return any ? ok : 1;
}

/* ------------------------------------------------------------------ */
/* directory tree                                                      */
/* ------------------------------------------------------------------ */

static void mark_lists(void);

static Dir *new_dir(Dir *parent, const char *name, dev_t dev)
{
    Dir *d = xmalloc(sizeof *d);
    memset(d, 0, sizeof *d);
    d->name = xstrdup(name);
    d->parent = parent;
    d->dev = dev;
    return d;
}

static Dir *find_kid(Dir *d, const char *name)
{
    int lo = 0, hi = d->nkids - 1;
    while (lo <= hi) {
        int mid = (lo + hi) / 2;
        int c = cmpstr(name, d->kids[mid]->name);
        if (!c) return d->kids[mid];
        if (c < 0) hi = mid - 1; else lo = mid + 1;
    }
    return NULL;
}

static FileEnt *find_file(Dir *d, const char *name)
{
    int lo = 0, hi = d->nfiles - 1;
    while (lo <= hi) {
        int mid = (lo + hi) / 2;
        int c = cmpstr(name, d->files[mid].name);
        if (!c) return &d->files[mid];
        if (c < 0) hi = mid - 1; else lo = mid + 1;
    }
    return NULL;
}

static int is_under(Dir *x, Dir *anc)
{
    for (; x; x = x->parent) if (x == anc) return 1;
    return 0;
}

static void free_files(Dir *d)
{
    int i;
    for (i = 0; i < d->nfiles; i++) free(d->files[i].name);
    free(d->files);
    d->files = NULL;
    d->nfiles = 0;
}

static void free_dir(Dir *d)
{
    int i, j;
    for (i = 0; i < d->nkids; i++) free_dir(d->kids[i]);
    for (j = 0; j < 2; j++) if (P[j].seldir == d) P[j].seldir = NULL;
    free(d->kids);
    free_files(d);
    free(d->name);
    free(d);
}

static int cmp_fe(const void *a, const void *b)
{
    return cmpstr(((const FileEnt *)a)->name, ((const FileEnt *)b)->name);
}

static int cmp_dirp(const void *a, const void *b)
{
    return cmpstr((*(Dir * const *)a)->name, (*(Dir * const *)b)->name);
}

/* (re)read one directory, keeping tags and already-known subdirectories */
static void log_dir(Dir *d)
{
    char path[MAXP], cp[MAXP];
    DIR *dp;
    struct dirent *e;
    FileEnt *nf = NULL;
    int nn = 0, nc = 0;
    Dir **nk = NULL;
    int nkn = 0, nkc = 0, i, j;

    mark_lists();
    stats_dirty = 1;
    dir_path(d, path, sizeof path);
    for (i = 0; i < d->nkids; i++) d->kids[i]->mark = 0;
    d->err = 0;
    dp = opendir(path);
    if (!dp) {
        d->err = errno ? errno : EACCES;
    } else {
        while ((e = readdir(dp)) != NULL) {
            struct stat st;
            if (!strcmp(e->d_name, ".") || !strcmp(e->d_name, "..")) continue;
            join_path(cp, sizeof cp, path, e->d_name);
            if (lstat(cp, &st) < 0) {
                memset(&st, 0, sizeof st);
                st.st_mode = S_IFREG;
            }
            if (S_ISDIR(st.st_mode)) {
                Dir *k = find_kid(d, e->d_name);
                if (k) { k->mark = 1; k->dev = st.st_dev; }
                else k = new_dir(d, e->d_name, st.st_dev);
                if (nkn == nkc) { nkc = nkc ? nkc * 2 : 16; nk = xrealloc(nk, nkc * sizeof *nk); }
                nk[nkn++] = k;
            } else {
                FileEnt *f;
                if (nn == nc) { nc = nc ? nc * 2 : 32; nf = xrealloc(nf, nc * sizeof *nf); }
                f = &nf[nn++];
                f->name = xstrdup(e->d_name);
                f->size = st.st_size;
                f->mtime = st.st_mtime;
                f->mode = st.st_mode;
                f->uid = st.st_uid;
                f->gid = st.st_gid;
                f->tagged = 0;
                f->dir = d;
            }
        }
        closedir(dp);
    }
    if (nn) qsort(nf, nn, sizeof *nf, cmp_fe);
    for (i = 0; i < nn; i++) {
        FileEnt *o = find_file(d, nf[i].name);
        if (o) nf[i].tagged = o->tagged;
    }
    free_files(d);
    d->files = nf;
    d->nfiles = nn;

    /* drop subdirectories that went away */
    for (i = 0; i < d->nkids; i++) {
        Dir *k = d->kids[i];
        if (!k->mark) {
            for (j = 0; j < 2; j++) if (P[j].cur && is_under(P[j].cur, k)) P[j].cur = d;
            free_dir(k);
        }
    }
    free(d->kids);
    if (nkn) qsort(nk, nkn, sizeof *nk, cmp_dirp);
    d->kids = nk;
    d->nkids = nkn;
    d->logged = 1;
}

static void relog_branch(Dir *d)
{
    int i;
    log_dir(d);
    for (i = 0; i < d->nkids; i++)
        if (d->kids[i]->logged) relog_branch(d->kids[i]);
}

/* walk to a path, logging and expanding as we go */
static Dir *goto_path(const char *path)
{
    char buf[MAXP], *tok;
    Dir *d = root;
    scopy(buf, path, sizeof buf);
    for (tok = strtok(buf, "/"); tok; tok = strtok(NULL, "/")) {
        Dir *k;
        if (!d->logged) log_dir(d);
        d->expanded = 1;
        k = find_kid(d, tok);
        if (!k) break;
        d = k;
    }
    if (!d->logged) log_dir(d);
    return d;
}

/* find a logged directory by path without logging anything */
static Dir *dir_lookup(const char *path)
{
    char buf[MAXP], *tok;
    Dir *d = root;
    scopy(buf, path, sizeof buf);
    for (tok = strtok(buf, "/"); tok; tok = strtok(NULL, "/")) {
        if (!d->logged) return NULL;
        d = find_kid(d, tok);
        if (!d) return NULL;
    }
    return d;
}

static void relog_path(const char *path)
{
    Dir *d = dir_lookup(path);
    if (d && d->logged) log_dir(d);
}

static void relog_parent_of(const char *path)
{
    char buf[MAXP];
    char *s;
    scopy(buf, path, sizeof buf);
    s = strrchr(buf, '/');
    if (!s) return;
    if (s == buf) s[1] = 0; else *s = 0;
    relog_path(buf);
}

static void vis_add(Dir *d)
{
    int i;
    if (nvis == cvis) { cvis = cvis ? cvis * 2 : 256; vis = xrealloc(vis, cvis * sizeof *vis); }
    vis[nvis++] = d;
    if (d->expanded) for (i = 0; i < d->nkids; i++) vis_add(d->kids[i]);
}

static void build_vis(void)
{
    nvis = 0;
    vis_add(root);
}

static int vis_index(Dir *d)
{
    int i;
    for (i = 0; i < nvis; i++) if (vis[i] == d) return i;
    return 0;
}

static void fix_cur_visible(Pane *p)
{
    Dir *x, *cand = NULL;
    for (x = p->cur->parent; x; x = x->parent) if (!x->expanded) cand = x;
    if (cand) p->cur = cand;
}

static int depth_of(Dir *d)
{
    int n = 0;
    while (d->parent) { n++; d = d->parent; }
    return n;
}

static int is_last(Dir *d)
{
    return !d->parent || d->parent->kids[d->parent->nkids - 1] == d;
}

/* ------------------------------------------------------------------ */
/* file lists and statistics                                           */
/* ------------------------------------------------------------------ */

static void mark_lists(void)
{
    int i;
    if (lists_dirty) return;
    for (i = 0; i < npanes; i++) {
        Pane *p = &P[i];
        if (p->nfl > 0 && p->fsel >= 0 && p->fsel < p->nfl) {
            scopy(p->selname, p->fl[p->fsel]->name, sizeof p->selname);
            p->seldir = p->fl[p->fsel]->dir;
        } else {
            p->selname[0] = 0;
            p->seldir = NULL;
        }
    }
    lists_dirty = 1;
}

static const char *ext_of(const char *n)
{
    const char *e = strrchr(n, '.');
    return (e && e != n) ? e + 1 : "";
}

static int cmp_list(const void *a, const void *b)
{
    const FileEnt *x = *(FileEnt * const *)a, *y = *(FileEnt * const *)b;
    int r = 0;
    switch (sortmode) {
    case 1: r = cmpstr(ext_of(x->name), ext_of(y->name)); break;
    case 2: r = (x->size < y->size) ? -1 : (x->size > y->size); break;
    case 3: r = (x->mtime < y->mtime) ? -1 : (x->mtime > y->mtime); break;
    }
    if (!r) r = cmpstr(x->name, y->name);
    if (!r) r = (x->dir < y->dir) ? -1 : (x->dir > y->dir);
    return r;
}

static void list_add_dir(Pane *p, Dir *d, int recurse)
{
    int i;
    for (i = 0; i < d->nfiles; i++) {
        FileEnt *f = &d->files[i];
        if (!matches(f->name)) continue;
        if (p->tagonly && !f->tagged) continue;
        if (p->nfl == p->fcap) {
            p->fcap = p->fcap ? p->fcap * 2 : 64;
            p->fl = xrealloc(p->fl, p->fcap * sizeof *p->fl);
        }
        p->fl[p->nfl++] = f;
    }
    if (recurse) for (i = 0; i < d->nkids; i++) list_add_dir(p, d->kids[i], 1);
}

static void build_list(Pane *p)
{
    int i;
    p->nfl = 0;
    if (p->lmode == 0) list_add_dir(p, p->cur, 0);
    else if (p->lmode == 1) list_add_dir(p, p->cur, 1);
    else list_add_dir(p, root, 1);
    if (p->nfl > 1 && (sortmode || p->lmode)) qsort(p->fl, p->nfl, sizeof *p->fl, cmp_list);
    if (p->selname[0]) {
        for (i = 0; i < p->nfl; i++)
            if (!strcmp(p->fl[i]->name, p->selname) && (!p->seldir || p->fl[i]->dir == p->seldir)) {
                p->fsel = i;
                break;
            }
    }
    if (p->fsel >= p->nfl) p->fsel = p->nfl - 1;
    if (p->fsel < 0) p->fsel = 0;
}

static void rebuild_lists(void)
{
    int i;
    for (i = 0; i < npanes; i++) {
        if (!P[i].cur->logged) log_dir(P[i].cur);
    }
    for (i = 0; i < npanes; i++) build_list(&P[i]);
    lists_dirty = 0;
}

static void stats_walk(Dir *d)
{
    int i;
    ST.dirs++;
    for (i = 0; i < d->nfiles; i++) {
        FileEnt *f = &d->files[i];
        ST.files++;
        ST.bytes += f->size;
        if (matches(f->name)) {
            ST.mfiles++;
            ST.mbytes += f->size;
            if (f->tagged) { ST.tfiles++; ST.tbytes += f->size; }
        }
    }
    for (i = 0; i < d->nkids; i++) if (d->kids[i]->logged) stats_walk(d->kids[i]);
}

static void compute_stats(void)
{
    memset(&ST, 0, sizeof ST);
    stats_walk(root);
    stats_dirty = 0;
}

static FileEnt *cur_file(Pane *p)
{
    if (lists_dirty) rebuild_lists();
    if (p->nfl <= 0 || p->fsel < 0 || p->fsel >= p->nfl) return NULL;
    return p->fl[p->fsel];
}

/* ------------------------------------------------------------------ */
/* drawing primitives                                                  */
/* ------------------------------------------------------------------ */

static int strcols(const char *s)
{
    int n = 0;
    for (; *s; s++) if (!utf8 || ((unsigned char)*s & 0xC0) != 0x80) n++;
    return n;
}

/* draw a string clipped to maxw columns; returns columns used */
static int putsn(int y, int x, const char *s, int maxw, chtype a)
{
    int n = 0;
    if (maxw <= 0) return 0;
    attrset(a);
    move(y, x);
    for (; *s && n < maxw; s++) {
        unsigned char c = (unsigned char)*s;
        if (utf8 && (c & 0xC0) == 0x80) continue;
        if (c >= 32 && c < 127) addch(c);
        else if (!utf8 && c >= 160) addch(c);
        else addch('?');
        n++;
    }
    return n;
}

/* same, but mark truncation with '~' */
static int putst(int y, int x, const char *s, int maxw, chtype a)
{
    int n;
    if (maxw <= 0) return 0;
    if (strcols(s) <= maxw) return putsn(y, x, s, maxw, a);
    n = putsn(y, x, s, maxw - 1, a);
    addch('~');
    return n + 1;
}

/* draw a string keeping its tail when too long */
static void putstail(int y, int x, const char *s, int maxw, chtype a)
{
    int c = strcols(s);
    if (c <= maxw) { putsn(y, x, s, maxw, a); return; }
    attrset(a);
    mvaddstr(y, x, "...");
    while (c > maxw - 3) {
        s++;
        if (!utf8 || ((unsigned char)*s & 0xC0) != 0x80) c--;
    }
    putsn(y, x + 3, s, maxw - 3, a);
}

static void fill(int y, int x, int n, chtype a)
{
    int i;
    if (n <= 0) return;
    attrset(a);
    move(y, x);
    for (i = 0; i < n; i++) addch(' ');
}

static void put_enter_glyph(chtype a)
{
    attrset(a);
    addch('<');
    addch(ACS_LRCORNER);
}

/* text with {hot} segments; \001 = Enter glyph, \002 = up arrow */
static int put_marked(int y, int x, const char *s, int maxx)
{
    int hot = 0;
    move(y, x);
    for (; *s; s++) {
        int cx, cy;
        getyx(stdscr, cy, cx);
        (void)cy;
        if (cx >= maxx) break;
        if (*s == '{') { hot = 1; continue; }
        if (*s == '}') { hot = 0; continue; }
        if (*s == '\001') { put_enter_glyph(hot ? AH : AN); continue; }
        if (*s == '\002') { attrset(hot ? AH : AN); addch(ACS_UARROW); continue; }
        attrset(hot ? AH : AN);
        addch((unsigned char)*s);
    }
    {
        int cx, cy;
        getyx(stdscr, cy, cx);
        (void)cy;
        return cx;
    }
}

static int marked_len(const char *s)
{
    int n = 0;
    for (; *s; s++) {
        if (*s == '{' || *s == '}') continue;
        n += (*s == '\001') ? 2 : 1;
    }
    return n;
}

static int is_hline(int y, int x)
{
    chtype c = mvinch(y, x);
    return (c & A_CHARTEXT) == (ACS_HLINE & A_CHARTEXT);
}

/* turn plain vertical lines into tees where horizontal lines meet them */
static void fix_junction(int y, int x)
{
    int l = x > 0 && is_hline(y, x - 1);
    int r = x < W - 1 && is_hline(y, x + 1);
    attrset(AN);
    if (l && r) mvaddch(y, x, ACS_PLUS);
    else if (l) mvaddch(y, x, ACS_RTEE);
    else if (r) mvaddch(y, x, ACS_LTEE);
}

static void draw_clock(void)
{
    char b[64];
    fmt_date(time(NULL), b);
    putsn(0, W - 1 - (int)strlen(b), b, (int)strlen(b), AN);
}

/* ------------------------------------------------------------------ */
/* main screen                                                         */
/* ------------------------------------------------------------------ */

static void draw_tree(Pane *p, int y0, int x0, int h, int w, int active)
{
    int ci, r;
    Dir *chain[1024];
    fix_cur_visible(p);
    ci = vis_index(p->cur);
    if (p->ttop > ci) p->ttop = ci;
    if (ci >= p->ttop + h) p->ttop = ci - h + 1;
    if (p->ttop > nvis - h) p->ttop = nvis - h;
    if (p->ttop < 0) p->ttop = 0;
    for (r = 0; r < h && p->ttop + r < nvis; r++) {
        Dir *d = vis[p->ttop + r], *x;
        int depth = depth_of(d), lvl, cx = x0 + 1, k, maxx = x0 + w - 1;
        const char *nm;
        int y = y0 + r, barw;
        if (depth > 1023) depth = 1023;
        for (x = d, k = depth; k >= 0 && x; x = x->parent, k--) chain[k] = x;
        attrset(AN);
        for (lvl = 1; lvl < depth && cx + 3 <= maxx; lvl++) {
            if (!is_last(chain[lvl])) mvaddch(y, cx, ACS_VLINE);
            cx += 3;
        }
        if (depth > 0 && cx + 3 <= maxx) {
            mvaddch(y, cx, is_last(d) ? ACS_LLCORNER : ACS_LTEE);
            mvaddch(y, cx + 1, ACS_HLINE);
            if (d->logged && d->nkids && !d->expanded) mvaddch(y, cx + 2, '+');
            else mvaddch(y, cx + 2, ACS_HLINE);
            cx += 3;
        }
        nm = depth ? d->name : "/";
        if (cx >= maxx) continue;
        barw = strcols(nm) + 1;
        if (barw < 13) barw = 13;
        if (cx + barw > maxx) barw = maxx - cx;
        if (d == p->cur) {
            chtype a = active ? AB : AI;
            fill(y, cx, barw, a);
            putst(y, cx, nm, barw, a);
        } else {
            putst(y, cx, nm, maxx - cx, d->logged ? AN : AD);
        }
    }
}

static void draw_fcell(int y, int x, int w, FileEnt *f, int sel, int active)
{
    chtype a = sel ? (active ? AB : AI) : AN;
    if (w < 3) return;
    if (f->tagged) { attrset(AH); mvaddch(y, x, ACS_DIAMOND); }
    if (sel) fill(y, x + 1, w - 1, a);
    putst(y, x + 1, f->name, w - 1, a);
}

static void draw_fperm(int y, int x, int w, FileEnt *f, int sel, int active)
{
    char md[16];
    chtype a = sel ? (active ? AB : AI) : AN;
    if (w < 16) { draw_fcell(y, x, w, f, sel, active); return; }
    lsmode(f->mode, md);
    if (f->tagged) { attrset(AH); mvaddch(y, x, ACS_DIAMOND); }
    if (sel) fill(y, x + 1, w - 1, a);
    putst(y, x + 1, f->name, w - 13, a);
    putsn(y, x + w - 11, md, 10, a);
}

static void draw_fdetail(int y, int x, int w, FileEnt *f, int sel, int active)
{
    char sz[32], dt[32], md[16], line[96];
    chtype a = sel ? (active ? AB : AI) : AN;
    int namew, tail;
    if (S_ISDIR(f->mode)) strcpy(sz, "<DIR>");
    else commas((long long)f->size, sz);
    fmt_date(f->mtime, dt);
    lsmode(f->mode, md);
    if (w >= 52) sprintf(line, " %9s %s  %s", sz, md, dt);
    else sprintf(line, " %s  %s", md, dt);
    tail = strlen(line);
    namew = w - 1 - tail;
    if (namew < 8) { namew = w - 1; tail = 0; }
    if (f->tagged) { attrset(AH); mvaddch(y, x, ACS_DIAMOND); }
    if (sel) fill(y, x + 1, w - 1, a);
    putst(y, x + 1, f->name, namew, a);
    if (tail) putsn(y, x + 1 + namew, line, tail, a);
}

static void draw_files(Pane *p, int y0, int x0, int h, int w, int cursor, int active, int forcecols)
{
    int colw = 18, ncol, c, r, i;
    if (h <= 0 || w <= 2) return;
    x0++; w -= 2;
    if (forcecols == 1 || fmtmode == 2) ncol = 1, colw = w;
    else {
        if (fmtmode == 1) colw = 28;
        ncol = w / colw;
        if (ncol < 1) ncol = 1;
        colw = w / ncol;
    }
    p->vrows = h;
    p->vcols = ncol;
    if (cursor) {
        if (p->fsel < p->ftop) p->ftop = (p->fsel / h) * h;
        if (p->fsel >= p->ftop + h * ncol) p->ftop = (p->fsel / h - ncol + 1) * h;
        if (p->ftop < 0) p->ftop = 0;
    } else p->ftop = 0;
    if (p->nfl == 0) {
        const char *m = p->cur->err ? strerror(p->cur->err) : "No files!";
        if (p->lmode || p->cur->nfiles) m = "No matching files";
        putsn(y0 + h / 2, x0 + (w - (int)strlen(m)) / 2, m, w, AN);
        return;
    }
    for (c = 0; c < ncol; c++)
        for (r = 0; r < h; r++) {
            i = p->ftop + c * h + r;
            if (i >= p->nfl) return;
            if (forcecols == 1)
                draw_fcell(y0 + r, x0, colw - 1, p->fl[i], cursor && i == p->fsel, active);
            else if (fmtmode == 2)
                draw_fdetail(y0 + r, x0, colw, p->fl[i], cursor && i == p->fsel, active);
            else if (fmtmode == 1)
                draw_fperm(y0 + r, x0 + c * colw, colw - 1, p->fl[i], cursor && i == p->fsel, active);
            else
                draw_fcell(y0 + r, x0 + c * colw, colw - 1, p->fl[i], cursor && i == p->fsel, active);
        }
}

/* ---- autoview ---- */

static struct {
    char path[MAXP];
    time_t mtime;
    off_t size;
    char *buf;
    int len;
    int err;
} AV;

static void av_load(FileEnt *f)
{
    char path[MAXP];
    struct stat st;
    int fd, n;
    file_path(f, path, sizeof path);
    if (!strcmp(path, AV.path) && AV.mtime == f->mtime && AV.size == f->size) return;
    scopy(AV.path, path, sizeof AV.path);
    AV.mtime = f->mtime;
    AV.size = f->size;
    AV.len = 0;
    AV.err = 0;
    if (!AV.buf) AV.buf = xmalloc(16384);
    if (lstat(path, &st) < 0 || !S_ISREG(st.st_mode)) { AV.err = -1; return; }
    fd = open(path, O_RDONLY | O_NONBLOCK);
    if (fd < 0) { AV.err = errno; return; }
    n = read(fd, AV.buf, 16384);
    close(fd);
    AV.len = n > 0 ? n : 0;
}

static int is_binary(const char *b, int n)
{
    int i;
    if (n > 1024) n = 1024;
    for (i = 0; i < n; i++) if (b[i] == 0) return 1;
    return 0;
}

static int render_text_line(int y, int x, int w, const char *s, int len, int hoff, chtype a)
{
    int col = 0, i, out = 0;
    attrset(a);
    move(y, x);
    for (i = 0; i < len && out < w; i++) {
        unsigned char c = (unsigned char)s[i];
        if (c == '\r' && i == len - 1) break;
        if (c == '\t') {
            int nx = (col / 8 + 1) * 8;
            while (col < nx && out < w) { if (col >= hoff) { addch(' '); out++; } col++; }
            continue;
        }
        if (utf8 && (c & 0xC0) == 0x80) continue;
        if (col >= hoff) {
            if (c >= 32 && c < 127) addch(c);
            else if (!utf8 && c >= 160) addch(c);
            else if (utf8 && c >= 0xC0) addch('?');
            else addch('.');
            out++;
        }
        col++;
    }
    return out;
}

static void render_hex_line(int y, int x, int w, const unsigned char *d, long long off, int n)
{
    char b[100];
    int i, p;
    p = sprintf(b, "%08llx  ", off);
    for (i = 0; i < 16; i++) {
        if (i < n) p += sprintf(b + p, "%02x ", d[i]);
        else p += sprintf(b + p, "   ");
        if (i == 7) b[p++] = ' ';
    }
    b[p++] = ' ';
    for (i = 0; i < n; i++) b[p++] = (d[i] >= 32 && d[i] < 127) ? d[i] : '.';
    b[p] = 0;
    putsn(y, x, b, w, AN);
}

static void draw_autoview(Pane *p, int y0, int x0, int h, int w)
{
    FileEnt *f = cur_file(p);
    int r, pos = 0;
    if (!f) return;
    av_load(f);
    if (AV.err) {
        putsn(y0, x0 + 1, AV.err < 0 ? "(not a regular file)" : strerror(AV.err), w - 2, AD);
        return;
    }
    if (is_binary(AV.buf, AV.len)) {
        int bw = w - 2;
        for (r = 0; r < h && pos < AV.len; r++, pos += 16) {
            int n = AV.len - pos;
            if (n > 16) n = 16;
            if (bw >= 76) render_hex_line(y0 + r, x0 + 1, bw, (unsigned char *)AV.buf + pos, pos, n);
            else {
                char b[80];
                int i, q = sprintf(b, "%06x ", pos);
                for (i = 0; i < n && q < 76; i++) q += sprintf(b + q, "%02x", (unsigned char)AV.buf[pos + i]);
                putsn(y0 + r, x0 + 1, b, bw, AN);
            }
        }
        return;
    }
    for (r = 0; r < h && pos < AV.len; r++) {
        int e = pos;
        while (e < AV.len && AV.buf[e] != '\n') e++;
        render_text_line(y0 + r, x0 + 1, w - 2, AV.buf + pos, e - pos, 0, AN);
        pos = e + 1;
    }
}

/* ---- right hand info panel ---- */

static void info_row(int y, int px, const char *label, long long v)
{
    char b[48];
    int lw = strlen(label);
    numfit(v, RW - lw - 2, b);
    putsn(y, px, label, lw, AN);
    putsn(y, px + RW - (int)strlen(b), b, RW, AN);
}

static void draw_info(int px)
{
    Pane *p = &P[ap];
    char b[MAXP], n[48];
    int y = 2, ylim = H - 5;
    const char *title;

    if (stats_dirty) compute_stats();
    putsn(y, px, "FILE", 4, AN);
    putst(y, px + 6, specstr, RW - 6, AN);
    y++;
    attrset(AN); mvhline(y, px, ACS_HLINE, RW); y++;
    dir_path(p->cur, b, sizeof b);
    update_disk(b);
    putsn(y, px, "DISK", 4, AN);
    putstail(y, px + 6, DK.dev, RW - 6, AN);
    y++;
    putsn(y++, px, " Available", RW, AN);
    if (DK.avail >= 0) info_row(y, px, "  Bytes", DK.avail);
    else putsn(y, px, "  Bytes  ?", RW, AN);
    y++;
    attrset(AN); mvhline(y, px, ACS_HLINE, RW); y++;
    title = p->fmode ? (p->lmode == 1 ? "BRANCH Statistics" : p->lmode == 2 ? "SHOWALL Statistics"
                                                                            : "DIR Statistics")
                     : "DISK Statistics";
    putsn(y++, px, title, RW, AN);
    if (y > ylim) return;
    putsn(y++, px, " Total", RW, AN);
    if (y > ylim) return;
    info_row(y++, px, "  Files", ST.files);
    if (y > ylim) return;
    info_row(y++, px, "  Bytes", ST.bytes);
    if (y > ylim) return;
    putsn(y++, px, " Matching", RW, AN);
    if (y > ylim) return;
    info_row(y++, px, "  Files", ST.mfiles);
    if (y > ylim) return;
    info_row(y++, px, "  Bytes", ST.mbytes);
    if (y > ylim) return;
    putsn(y++, px, " Tagged", RW, AN);
    if (y > ylim) return;
    info_row(y++, px, "  Files", ST.tfiles);
    if (y > ylim) return;
    info_row(y++, px, "  Bytes", ST.tbytes);
    if (y > ylim) return;
    if (!p->fmode) {
        long long cb = 0;
        int i;
        for (i = 0; i < p->cur->nfiles; i++)
            if (matches(p->cur->files[i].name)) cb += p->cur->files[i].size;
        putsn(y++, px, " Current Directory", RW, AN);
        if (y > ylim) return;
        putstail(y++, px + 2, b, RW - 2, AN);
        if (y > ylim) return;
        info_row(y++, px, "  Bytes", cb);
    } else {
        FileEnt *f = cur_file(p);
        putsn(y++, px, " Current File", RW, AN);
        if (!f || y > ylim) return;
        putst(y++, px + 2, f->name, RW - 2, AN);
        if (y > ylim) return;
        info_row(y++, px, "  Bytes", (long long)f->size);
        if (y > ylim) return;
        fmt_date_short(f->mtime, n);
        putsn(y++, px + 2, n, RW - 2, AN);
        if (y > ylim) return;
        lsmode(f->mode, n);
        putsn(y++, px + 2, n, RW - 2, AN);
        if (y > ylim) return;
        if (p->lmode) {
            dir_path(f->dir, b, sizeof b);
            putstail(y++, px + 2, b, RW - 2, AN);
        }
    }
}

/* ---- command lines ---- */

static void draw_cmdrow(int y, const char *label, const char *items)
{
    putsn(y, 0, label, 10, AN);
    put_marked(y, 10, items, W - 1);
}

static void draw_cmds(void)
{
    Pane *p = &P[ap];
    int i;
    for (i = H - 3; i < H; i++) fill(i, 0, W, AN);
    if (show_about) {
        const char *l1 = "TTreeAu (tm) Version " TTA_VERSION " for Linux   All Rights Reserved Worldwide";
        const char *l2 = "Copyright (c) 1989-1993, 2026 Paul Khoury";
        putsn(H - 2, (W - (int)strlen(l1)) / 2, l1, W, AN);
        putsn(H - 1, (W - (int)strlen(l2)) / 2, l2, W, AN);
        return;
    }
    if (!p->fmode) {
        draw_cmdrow(H - 3, "DIR", "{A}vail  {B}ranch  {C}ompare  {D}elete  {F}ilespec  {G}lobal  {I}nvert  {L}og  {M}ake");
        draw_cmdrow(H - 2, "COMMANDS", "{O}ops!  {P}rint  {R}ename  {S}howall  {T}ag  {U}ntag  {V}olume  e{X}ecute  {Q}uit");
        put_marked(H - 1, 0, "{\001} file  {F7} autoview  {F8} split  {F9} menu  {F10} commands  {F1} help  {?} stats", W - 1);
    } else {
        const char *lbl = p->lmode == 1 ? "BRANCH" : p->lmode == 2 ? "SHOWALL" : "FILE";
        draw_cmdrow(H - 3, lbl, "{A}ttributes  {C}opy  {D}elete  {E}dit  {F}ilespec  {I}nvert  {M}ove  {N}ew date");
        draw_cmdrow(H - 2, "COMMANDS", "{L}og  {O}pen  {P}rint  {R}ename  {T}ag  {U}ntag  {V}iew  e{X}ecute  {Q}uit");
        put_marked(H - 1, 0, "{\001} tree  {F7} autoview  {F8} split  {Alt+F} display  {F10} commands  {Shift} tagged", W - 1);
    }
}

static int too_small(void)
{
    return W < 60 || H < 16;
}

static void draw_main(void)
{
    int sx, px, lw, i, ih = H - 6, x;
    int px0[2], pw[2], vsep = -1;
    char path[MAXP];
    Pane *p;

    W = COLS; H = LINES;
    ih = H - 6;
    erase();
    if (too_small()) {
        putsn(0, 0, "Window too small for TTreeAu (need 60x16)", W, AN);
        return;
    }
    if (lists_dirty) rebuild_lists();
    build_vis();
    p = &P[ap];

    /* path line */
    if (p->fmode && cur_file(p)) dir_path(cur_file(p)->dir, path, sizeof path);
    else dir_path(p->cur, path, sizeof path);
    putsn(0, 1, "Path:", 5, AN);
    putstail(0, 7, path, W - 30, AN);
    draw_clock();

    /* frame */
    sx = W - RW - 2;
    px = sx + 1;
    lw = sx - 1;
    attrset(AN);
    mvaddch(1, 0, ACS_ULCORNER);
    mvhline(1, 1, ACS_HLINE, W - 2);
    mvaddch(1, W - 1, ACS_URCORNER);
    mvvline(2, 0, ACS_VLINE, ih);
    mvvline(2, W - 1, ACS_VLINE, ih);
    mvvline(2, sx, ACS_VLINE, ih);
    mvaddch(H - 4, 0, ACS_LLCORNER);
    mvhline(H - 4, 1, ACS_HLINE, W - 2);
    mvaddch(H - 4, W - 1, ACS_LRCORNER);
    mvaddch(1, sx, ACS_TTEE);
    mvaddch(H - 4, sx, ACS_BTEE);

    if (npanes == 2) {
        pw[0] = (lw - 1) / 2;
        px0[0] = 1;
        vsep = 1 + pw[0];
        px0[1] = vsep + 1;
        pw[1] = lw - pw[0] - 1;
        attrset(AN);
        mvvline(2, vsep, ACS_VLINE, ih);
        mvaddch(1, vsep, ACS_TTEE);
        mvaddch(H - 4, vsep, ACS_BTEE);
    } else {
        px0[0] = 1;
        pw[0] = lw;
    }

    for (i = 0; i < npanes; i++) {
        Pane *q = &P[i];
        int act = (i == ap);
        x = px0[i];
        if (q->fmode) {
            if (autoview && act) {
                int lw3 = pw[i] / 3;
                if (lw3 < 16) lw3 = 16;
                draw_files(q, 2, x, ih, lw3, 1, act, 1);
                attrset(AN);
                mvvline(2, x + lw3, ACS_VLINE, ih);
                mvaddch(1, x + lw3, ACS_TTEE);
                mvaddch(H - 4, x + lw3, ACS_BTEE);
                draw_autoview(q, 2, x + lw3 + 1, ih, pw[i] - lw3 - 1);
            } else {
                draw_files(q, 2, x, ih, pw[i], 1, act, 0);
            }
        } else {
            int nf = (ih + 1) / 5, th;
            if (nf < 2) nf = 2;
            th = ih - nf - 1;
            draw_tree(q, 2, x, th, pw[i], act);
            attrset(AN);
            mvhline(2 + th, x, ACS_HLINE, pw[i]);
            draw_files(q, 3 + th, x, nf, pw[i], 0, act, 0);
        }
    }

    draw_info(px);
    attrset(AN);
    mvhline(3, px, ACS_HLINE, RW);
    for (i = 2; i < H - 4; i++) {
        fix_junction(i, 0);
        fix_junction(i, sx);
        fix_junction(i, W - 1);
        if (vsep >= 0) fix_junction(i, vsep);
    }
    draw_cmds();
}

/* ------------------------------------------------------------------ */
/* keyboard                                                            */
/* ------------------------------------------------------------------ */

static int csi_map(int n)
{
    switch (n) {
    case 1: case 7: return KEY_HOME;
    case 2: return KEY_IC;
    case 3: return KEY_DC;
    case 4: case 8: return KEY_END;
    case 5: return KEY_PPAGE;
    case 6: return KEY_NPAGE;
    case 11: return K_F(1);
    case 12: return K_F(2);
    case 13: return K_F(3);
    case 14: return K_F(4);
    case 15: return K_F(5);
    case 17: return K_F(6);
    case 18: return K_F(7);
    case 19: return K_F(8);
    case 20: return K_F(9);
    case 21: return K_F(10);
    case 23: return K_F(11);
    case 24: return K_F(12);
    }
    return 0;
}

static int letter_key(int c)
{
    switch (c) {
    case 'A': return KEY_UP;
    case 'B': return KEY_DOWN;
    case 'C': return KEY_RIGHT;
    case 'D': return KEY_LEFT;
    case 'H': return KEY_HOME;
    case 'F': return KEY_END;
    case 'P': return K_F(1);
    case 'Q': return K_F(2);
    case 'R': return K_F(3);
    case 'S': return K_F(4);
    }
    return 0;
}

/* Read a key.  Returns 0 on the 1 second timeout (so the clock can tick).
 * Escape sequences the terminfo entry does not know (PuTTY, Linux console)
 * are decoded here; ESC+key is reported as ALT(key). */
static int getkey(void)
{
    int c, d, n;
    timeout(1000);
    c = getch();
    if (c == ERR) return 0;
    if (c == KEY_RESIZE) return KEY_RESIZE;
    if (c != 27) return c;
    timeout(80);
    d = getch();
    if (d == ERR || d == 27) { timeout(1000); return 27; }
    if (d == '[' || d == 'O') {
        int e = getch();
        if (e == ERR) { timeout(1000); return ALT(d); }
        if (d == '[' && e == '[') {                 /* linux console F1-F5 */
            int f = getch();
            timeout(1000);
            if (f >= 'A' && f <= 'E') return K_F(f - 'A' + 1);
            return 0;
        }
        if (e >= '0' && e <= '9') {
            n = e - '0';
            for (;;) {
                e = getch();
                if (e >= '0' && e <= '9') n = n * 10 + (e - '0');
                else break;
            }
            while (e != ERR && e != '~' && !(e >= 'A' && e <= 'Z') && !(e >= 'a' && e <= 'z')) e = getch();
            timeout(1000);
            if (e == '~') return csi_map(n);
            if (e != ERR) return letter_key(e);
            return 0;
        }
        timeout(1000);
        n = letter_key(e);
        return n ? n : 0;
    }
    timeout(1000);
    if (d >= 'A' && d <= 'Z') d = d - 'A' + 'a';
    return ALT(d);
}

static int is_enter(int c)
{
    return c == '\n' || c == '\r' || c == KEY_ENTER;
}

/* ------------------------------------------------------------------ */
/* prompts in the command area                                         */
/* ------------------------------------------------------------------ */

typedef struct { char **v; int n; } Hist;
static Hist hgen, hexec;

static void hist_add(Hist *h, const char *s)
{
    if (!*s) return;
    if (h->n && !strcmp(h->v[h->n - 1], s)) return;
    h->v = xrealloc(h->v, (h->n + 1) * sizeof *h->v);
    h->v[h->n++] = xstrdup(s);
}

typedef void (*bgfn)(void);
static int ed_y, ed_x, ed_w;

static void complete_path(char *buf, int size, int *pos, const char *basedir)
{
    int ws = *pos, i, nmatch = 0;
    char word[MAXP], dirpart[MAXP], full[MAXP], best[MAXP], *slash;
    const char *pre;
    DIR *dp;
    struct dirent *e;
    size_t plen;
    while (ws > 0 && buf[ws - 1] != ' ') ws--;
    if (*pos - ws >= (int)sizeof word) return;
    memcpy(word, buf + ws, *pos - ws);
    word[*pos - ws] = 0;
    slash = strrchr(word, '/');
    if (slash) {
        int dl = slash - word;
        memcpy(dirpart, word, dl);
        dirpart[dl] = 0;
        pre = slash + 1;
        if (dl == 0) strcpy(full, "/");
        else expand_path(dirpart, basedir, full, sizeof full);
    } else {
        pre = word;
        scopy(full, basedir, sizeof full);
    }
    plen = strlen(pre);
    dp = opendir(full);
    if (!dp) { beep(); return; }
    best[0] = 0;
    while ((e = readdir(dp)) != NULL) {
        if (!strcmp(e->d_name, ".") || !strcmp(e->d_name, "..")) continue;
        if (strncmp(e->d_name, pre, plen)) continue;
        if (!nmatch) scopy(best, e->d_name, sizeof best);
        else {
            for (i = 0; best[i] && best[i] == e->d_name[i]; i++);
            best[i] = 0;
        }
        nmatch++;
    }
    closedir(dp);
    if (!nmatch) { beep(); return; }
    {
        char add[MAXP];
        int al;
        scopy(add, best + plen, sizeof add);
        if (nmatch == 1) {
            char tp[MAXP];
            struct stat st;
            join_path(tp, sizeof tp, full, best);
            if (stat(tp, &st) == 0 && S_ISDIR(st.st_mode)) strncat(add, "/", sizeof add - strlen(add) - 1);
        } else beep();
        al = strlen(add);
        if ((int)strlen(buf) + al >= size) return;
        memmove(buf + *pos + al, buf + *pos, strlen(buf + *pos) + 1);
        memcpy(buf + *pos, add, al);
        *pos += al;
    }
}

/* single line editor; returns 1 on Enter, 0 on ESC */
static int edit_line(char *buf, int size, int pos, Hist *h, const char *basedir, bgfn bg)
{
    int hi = h ? h->n : 0, c, len, start;
    char saved[MAXP];
    saved[0] = 0;
    if (pos < 0 || pos > (int)strlen(buf)) pos = strlen(buf);
    curs_set(1);
    for (;;) {
        len = strlen(buf);
        bg();
        if (ed_w < 2) ed_w = 2;
        start = 0;
        if (pos > ed_w - 1) start = pos - (ed_w - 1);
        fill(ed_y, ed_x, ed_w, AH);
        putsn(ed_y, ed_x, buf + start, ed_w, AH);
        move(ed_y, ed_x + (pos - start));
        refresh();
        c = getkey();
        if (c == 0 || c == KEY_RESIZE) continue;
        if (c == 27) { curs_set(0); return 0; }
        if (is_enter(c)) { curs_set(0); if (h) hist_add(h, buf); return 1; }
        switch (c) {
        case KEY_LEFT: if (pos > 0) pos--; break;
        case KEY_RIGHT: if (pos < len) pos++; break;
        case KEY_HOME: case CTL('a'): pos = 0; break;
        case KEY_END: case CTL('e'): pos = len; break;
        case KEY_BACKSPACE: case 127: case 8:
            if (pos > 0) { memmove(buf + pos - 1, buf + pos, len - pos + 1); pos--; }
            break;
        case KEY_DC: case CTL('d'):
            if (pos < len) memmove(buf + pos, buf + pos + 1, len - pos);
            break;
        case CTL('u'): buf[0] = 0; pos = 0; break;
        case CTL('k'): buf[pos] = 0; break;
        case '\t':
            if (basedir) complete_path(buf, size, &pos, basedir);
            break;
        case KEY_UP:
            if (h && hi > 0) {
                if (hi == h->n) scopy(saved, buf, sizeof saved);
                hi--;
                scopy(buf, h->v[hi], size);
                pos = strlen(buf);
            }
            break;
        case KEY_DOWN:
            if (h && hi < h->n) {
                hi++;
                scopy(buf, hi == h->n ? saved : h->v[hi], size);
                pos = strlen(buf);
            }
            break;
        default:
            if (c >= 32 && c < 256 && c != 127 && len + 1 < size) {
                memmove(buf + pos + 1, buf + pos, len - pos + 1);
                buf[pos++] = (char)c;
            }
        }
    }
}

static char pr_title[MAXP], pr_label[128];

static void bg_prompt(void)
{
    int i;
    const char *hint = "{\002} history  {Tab} complete  {\001} ok  {ESC} cancel";
    draw_main();
    for (i = H - 3; i < H; i++) fill(i, 0, W, AN);
    putst(H - 3, 0, pr_title, W - 1, AT);
    putsn(H - 2, 2, pr_label, W - 4, AN);
    put_marked(H - 1, W - 1 - marked_len(hint), hint, W - 1);
    ed_y = H - 2;
    ed_x = 3 + strlen(pr_label);
    ed_w = W - ed_x - 1;
}

static int prompt(const char *title, const char *label, char *buf, int size, Hist *h, const char *basedir)
{
    scopy(pr_title, title, sizeof pr_title);
    scopy(pr_label, label, sizeof pr_label);
    return edit_line(buf, size, -1, h ? h : &hgen, basedir, bg_prompt);
}

static void cmd_overlay(const char *l1, const char *l2, const char *hint)
{
    int i;
    for (i = H - 3; i < H; i++) fill(i, 0, W, AN);
    if (l1) putst(H - 3, 0, l1, W - 1, AT);
    if (l2) putst(H - 2, 2, l2, W - 3, AN);
    if (hint) put_marked(H - 1, W - 1 - marked_len(hint), hint, W - 1);
}

/* ask a question; returns the (lowercase) key pressed from keys, or 0 */
static int ask(const char *title, const char *q, const char *keys)
{
    int c;
    for (;;) {
        draw_main();
        cmd_overlay(title, q, "{ESC} cancel");
        refresh();
        c = getkey();
        if (c == 0 || c == KEY_RESIZE) continue;
        if (c == 27) return 0;
        if (c < 256 && strchr(keys, tolower(c))) return tolower(c);
        beep();
    }
}

static void msg(const char *fmt, ...)
{
    char b[1024];
    va_list ap_;
    int c;
    va_start(ap_, fmt);
    vsnprintf(b, sizeof b, fmt, ap_);
    va_end(ap_);
    for (;;) {
        draw_main();
        cmd_overlay(NULL, b, "Press any key to continue");
        refresh();
        c = getkey();
        if (c && c != KEY_RESIZE) return;
    }
}

static void status(const char *fmt, ...)
{
    char b[1024];
    va_list ap_;
    va_start(ap_, fmt);
    vsnprintf(b, sizeof b, fmt, ap_);
    va_end(ap_);
    cmd_overlay(NULL, b, NULL);
    refresh();
}

static int esc_pressed(void)
{
    int c;
    nodelay(stdscr, TRUE);
    c = getch();
    nodelay(stdscr, FALSE);
    return c == 27;
}

/* ------------------------------------------------------------------ */
/* popups and full screen text                                         */
/* ------------------------------------------------------------------ */

static int popup(const char *title, char **items, int n, int sel)
{
    int top = 0, c, i;
    if (n <= 0) return -1;
    for (;;) {
        int bw = strlen(title) + 4, bh, bx, by, vis_n;
        for (i = 0; i < n; i++) if ((int)strlen(items[i]) + 4 > bw) bw = strlen(items[i]) + 4;
        if (bw > W - 4) bw = W - 4;
        vis_n = n;
        if (vis_n > H - 8) vis_n = H - 8;
        bh = vis_n + 2;
        bx = (W - bw) / 2;
        by = (H - 4 - bh) / 2 + 1;
        if (sel < top) top = sel;
        if (sel >= top + vis_n) top = sel - vis_n + 1;
        draw_main();
        for (i = 0; i < bh; i++) fill(by + i, bx, bw, AN);
        attrset(AN);
        mvaddch(by, bx, ACS_ULCORNER);
        mvhline(by, bx + 1, ACS_HLINE, bw - 2);
        mvaddch(by, bx + bw - 1, ACS_URCORNER);
        mvvline(by + 1, bx, ACS_VLINE, bh - 2);
        mvvline(by + 1, bx + bw - 1, ACS_VLINE, bh - 2);
        mvaddch(by + bh - 1, bx, ACS_LLCORNER);
        mvhline(by + bh - 1, bx + 1, ACS_HLINE, bw - 2);
        mvaddch(by + bh - 1, bx + bw - 1, ACS_LRCORNER);
        putsn(by, bx + 2, title, bw - 4, AT);
        for (i = 0; i < vis_n; i++) {
            int k = top + i;
            if (k == sel) fill(by + 1 + i, bx + 1, bw - 2, AB);
            putsn(by + 1 + i, bx + 2, items[k], bw - 4, k == sel ? AB : AN);
        }
        cmd_overlay(NULL, NULL, "{\002} select  {\001} ok  {ESC} cancel");
        refresh();
        c = getkey();
        if (c == 0 || c == KEY_RESIZE) continue;
        if (c == 27) return -1;
        if (is_enter(c)) return sel;
        if (c == KEY_UP && sel > 0) sel--;
        else if (c == KEY_DOWN && sel < n - 1) sel++;
        else if (c == KEY_PPAGE) { sel -= vis_n; if (sel < 0) sel = 0; }
        else if (c == KEY_NPAGE) { sel += vis_n; if (sel > n - 1) sel = n - 1; }
        else if (c == KEY_HOME) sel = 0;
        else if (c == KEY_END) sel = n - 1;
    }
}

static void text_screen(const char *title, const char **lines, int n)
{
    int top = 0, c, i, rows;
    for (;;) {
        W = COLS; H = LINES;
        rows = H - 3;
        if (top > n - rows) top = n - rows;
        if (top < 0) top = 0;
        erase();
        putsn(0, 1, title, W - 30, AT);
        draw_clock();
        attrset(AN);
        mvhline(1, 0, ACS_HLINE, W);
        for (i = 0; i < rows && top + i < n; i++) put_marked(2 + i, 1, lines[top + i], W - 1);
        cmd_overlay(NULL, NULL, NULL);
        put_marked(H - 1, 0, "{\002} scroll  {PgUp}/{PgDn} page  {ESC} return", W - 1);
        refresh();
        c = getkey();
        if (c == 0 || c == KEY_RESIZE) continue;
        if (c == 27 || is_enter(c) || c == 'q' || c == 'Q' || c == K_F(1)) return;
        if (c == KEY_UP) top--;
        else if (c == KEY_DOWN) top++;
        else if (c == KEY_PPAGE) top -= rows;
        else if (c == KEY_NPAGE || c == ' ') top += rows;
        else if (c == KEY_HOME) top = 0;
        else if (c == KEY_END) top = n;
    }
}

/* ------------------------------------------------------------------ */
/* running programs                                                    */
/* ------------------------------------------------------------------ */

static void wait_raw_key(void)
{
    struct termios o, t;
    char ch;
    if (tcgetattr(0, &o) < 0) return;
    t = o;
    t.c_lflag &= ~(ICANON | ECHO);
    t.c_cc[VMIN] = 1;
    t.c_cc[VTIME] = 0;
    tcsetattr(0, TCSANOW, &t);
    if (read(0, &ch, 1) < 0) { }
    tcsetattr(0, TCSANOW, &o);
}

static void run_shell(const char *dir, const char *cmd, int pause)
{
    pid_t pid;
    struct sigaction ign, oint, oquit;
    const char *sh = getenv("SHELL");
    if (!sh || !*sh) sh = "/bin/sh";
    def_prog_mode();
    endwin();
    memset(&ign, 0, sizeof ign);
    ign.sa_handler = SIG_IGN;
    sigaction(SIGINT, &ign, &oint);
    sigaction(SIGQUIT, &ign, &oquit);
    pid = fork();
    if (pid == 0) {
        signal(SIGINT, SIG_DFL);
        signal(SIGQUIT, SIG_DFL);
        signal(SIGTSTP, SIG_DFL);
        if (chdir(dir) < 0) { }
        execl(sh, sh, "-c", cmd, (char *)0);
        execl("/bin/sh", "sh", "-c", cmd, (char *)0);
        _exit(127);
    } else if (pid > 0) {
        int st;
        while (waitpid(pid, &st, 0) < 0 && errno == EINTR);
    }
    sigaction(SIGINT, &oint, NULL);
    sigaction(SIGQUIT, &oquit, NULL);
    if (pause) {
        printf("\nPress any key to return to TTreeAu...");
        fflush(stdout);
        wait_raw_key();
    }
    reset_prog_mode();
    clearok(curscr, TRUE);
    refresh();
}

static void spawn_detached(const char *prog, const char *arg)
{
    pid_t pid = fork();
    if (pid == 0) {
        int fd;
        setsid();
        fd = open("/dev/null", O_RDWR);
        if (fd >= 0) { dup2(fd, 0); dup2(fd, 1); dup2(fd, 2); if (fd > 2) close(fd); }
        if (fork() == 0) {
            execlp(prog, prog, arg, (char *)0);
            _exit(127);
        }
        _exit(0);
    } else if (pid > 0) {
        int st;
        waitpid(pid, &st, 0);
    }
}

/* ---- the eXecute screen ---- */

static char ex_dir[MAXP];

static void bg_exec(void)
{
    char cell[4][64], b[32];
    time_t now = time(NULL);
    struct tm *tm = localtime(&now);
    long long fm = free_memory();
    int i, x, h12;
    const char *hint = "{\002} history  {Tab} complete  {\001} ok  {ESC} cancel";
    char pr[MAXP];

    W = COLS; H = LINES;
    erase();
    strftime(cell[0], sizeof cell[0], "%a %b %d, %Y", tm);
    h12 = tm->tm_hour % 12;
    if (!h12) h12 = 12;
    if (clock24) sprintf(cell[1], "%02d:%02d:%02d", tm->tm_hour, tm->tm_min, tm->tm_sec);
    else sprintf(cell[1], "%2d:%02d:%02d %s", h12, tm->tm_min, tm->tm_sec, tm->tm_hour < 12 ? "am" : "pm");
    if (fm >= 0) { human((double)fm, b); sprintf(cell[2], "%s Free Memory", b); }
    else strcpy(cell[2], "? Free Memory");
    update_disk(ex_dir);
    if (DK.avail >= 0) { human((double)DK.avail, b); sprintf(cell[3], "%s Disk Space", b); }
    else strcpy(cell[3], "? Disk Space");

    attrset(AN);
    mvaddch(0, 0, ACS_ULCORNER);
    mvhline(0, 1, ACS_HLINE, W - 2);
    mvaddch(0, W - 1, ACS_URCORNER);
    mvaddch(1, 0, ACS_VLINE);
    mvaddch(2, 0, ACS_LTEE);
    mvhline(2, 1, ACS_HLINE, W - 2);
    mvaddch(2, W - 1, ACS_RTEE);
    x = 1;
    for (i = 0; i < 4; i++) {
        int cw = strlen(cell[i]) + 4;
        if (x + cw >= W - 1) break;
        putsn(1, x + 2, cell[i], cw - 2, AN);
        x += cw;
        if (x < W - 1 && i < 3) {
            attrset(AN);
            mvaddch(0, x, ACS_TTEE);
            mvaddch(1, x, ACS_VLINE);
            mvaddch(2, x, ACS_BTEE);
            x++;
        }
    }
    if (W - 1 - x >= 12) putsn(1, W - 12, "TTreeAu", 7, AN);
    attrset(AN);
    mvaddch(1, W - 1, ACS_VLINE);
    mvaddch(3, 0, ACS_VLINE);
    mvaddch(3, W - 1, ACS_VLINE);
    mvaddch(4, 0, ACS_LLCORNER);
    mvhline(4, 1, ACS_HLINE, W - 2);
    mvaddch(4, W - 1, ACS_LRCORNER);

    snprintf(pr, sizeof pr, "%s>", ex_dir);
    if ((int)strlen(pr) > W / 2) {
        putstail(3, 2, pr, W / 2, AN);
        ed_x = 2 + W / 2;
    } else {
        putsn(3, 2, pr, W - 4, AN);
        ed_x = 2 + strlen(pr);
    }
    ed_y = 3;
    ed_w = W - 2 - ed_x;
    put_marked(H - 1, W - 1 - marked_len(hint), hint, W - 1);
}

static void save_exec_history(void)
{
    char p[MAXP];
    FILE *f;
    int i;
    const char *h = getenv("HOME");
    if (!h) return;
    snprintf(p, sizeof p, "%s/.tta_history", h);
    f = fopen(p, "w");
    if (!f) return;
    for (i = hexec.n > 200 ? hexec.n - 200 : 0; i < hexec.n; i++) fprintf(f, "%s\n", hexec.v[i]);
    fclose(f);
}

static void load_exec_history(void)
{
    char p[MAXP], line[MAXP];
    FILE *f;
    const char *h = getenv("HOME");
    if (!h) return;
    snprintf(p, sizeof p, "%s/.tta_history", h);
    f = fopen(p, "r");
    if (!f) return;
    while (fgets(line, sizeof line, f)) {
        line[strcspn(line, "\n")] = 0;
        hist_add(&hexec, line);
    }
    fclose(f);
}

static void do_execute(const char *dir, const char *preset)
{
    char buf[MAXP];
    Dir *d;
    scopy(ex_dir, dir, sizeof ex_dir);
    scopy(buf, preset ? preset : "", sizeof buf);
    if (!edit_line(buf, sizeof buf, 0, &hexec, dir, bg_exec)) return;
    save_exec_history();
    if (!buf[0]) return;
    run_shell(dir, buf, 1);
    d = dir_lookup(dir);
    if (d) log_dir(d);
}

/* ------------------------------------------------------------------ */
/* file viewer                                                         */
/* ------------------------------------------------------------------ */

static const char *memfind(const char *h, size_t hl, const char *n, size_t nl)
{
    size_t i;
    if (!nl || nl > hl) return NULL;
    for (i = 0; i + nl <= hl; i++)
        if (h[i] == n[0] && !memcmp(h + i, n, nl)) return h + i;
    return NULL;
}

static void view_file(const char *path)
{
    struct stat st;
    char *data = NULL, search[256] = "";
    size_t len = 0, cap = 0;
    long *lines = NULL, nlines = 0, lcap = 0, top = 0;
    int fd, hex, hoff = 0, c, r, rows;
    size_t i;
    long long found = -1;

    if (stat(path, &st) < 0) { msg("%s: %s", path, strerror(errno)); return; }
    if (!S_ISREG(st.st_mode)) { msg("%s is not a regular file", path); return; }
    fd = open(path, O_RDONLY);
    if (fd < 0) { msg("%s: %s", path, strerror(errno)); return; }
    status("Reading %s ...", path);
    for (;;) {
        ssize_t n;
        if (len + 65536 > cap) {
            cap = cap ? cap * 2 : 65536;
            data = xrealloc(data, cap);
        }
        n = read(fd, data + len, cap - len);
        if (n <= 0) break;
        len += n;
    }
    close(fd);
    lcap = 1024;
    lines = xmalloc(lcap * sizeof *lines);
    lines[nlines++] = 0;
    for (i = 0; i < len; i++)
        if (data[i] == '\n' && i + 1 < len) {
            if (nlines == lcap) { lcap *= 2; lines = xrealloc(lines, lcap * sizeof *lines); }
            lines[nlines++] = i + 1;
        }
    hex = is_binary(data, len > 4096 ? 4096 : (int)len);

    for (;;) {
        long total;
        char hdr[64], sz[32];
        W = COLS; H = LINES;
        rows = H - 3;
        total = hex ? (long)((len + 15) / 16) : nlines;
        if (top > total - rows) top = total - rows;
        if (top < 0) top = 0;
        erase();
        putsn(0, 1, "VIEW", 4, AT);
        commas((long long)len, sz);
        sprintf(hdr, "%s bytes  line %ld/%ld", sz, top + 1, total);
        putstail(0, 6, path, W - 8 - (int)strlen(hdr), AN);
        putsn(0, W - 1 - (int)strlen(hdr), hdr, W, AN);
        attrset(AN);
        mvhline(1, 0, ACS_HLINE, W);
        for (r = 0; r < rows && top + r < total; r++) {
            long ln = top + r;
            if (hex) {
                long long off = (long long)ln * 16;
                int n = len - off > 16 ? 16 : (int)(len - off);
                render_hex_line(2 + r, 1, W - 2, (unsigned char *)data + off, off, n);
            } else {
                long s = lines[ln], e = (ln + 1 < nlines) ? lines[ln + 1] - 1 : (long)len;
                if (e > s && data[e - 1] == '\n') e--;
                render_text_line(2 + r, 1, W - 2, data + s, e - s, hoff, AN);
            }
        }
        fill(H - 1, 0, W, AN);
        put_marked(H - 1, 0, "VIEW  {\002}/{PgUp}/{PgDn} scroll  {H}ex  {/} search  {N}ext  {ESC} return", W - 1);
        refresh();
        c = getkey();
        if (c == 0 || c == KEY_RESIZE) continue;
        if (c == 27 || is_enter(c) || c == 'q' || c == 'Q') break;
        switch (c) {
        case KEY_UP: top--; break;
        case KEY_DOWN: top++; break;
        case KEY_PPAGE: top -= rows; break;
        case KEY_NPAGE: case ' ': top += rows; break;
        case KEY_HOME: top = 0; hoff = 0; break;
        case KEY_END: top = total; break;
        case KEY_LEFT: hoff -= 8; if (hoff < 0) hoff = 0; break;
        case KEY_RIGHT: hoff += 8; break;
        case 'h': case 'H': case 'x': case 'X':
            if (hex) {
                long long off = (long long)top * 16;
                long lo = 0, hi = nlines - 1;
                while (lo < hi) { long m = (lo + hi + 1) / 2; if (lines[m] <= off) lo = m; else hi = m - 1; }
                top = lo;
            } else top = lines[top] / 16;
            hex = !hex;
            break;
        case '/': case 'f': case 'F': case 'n': case 'N': {
            const char *p;
            long long from;
            if ((c == '/' || c == 'f' || c == 'F' || !search[0])) {
                char t[256];
                scopy(t, search, sizeof t);
                scopy(pr_title, "SEARCH for:", sizeof pr_title);
                scopy(pr_label, "", sizeof pr_label);
                {
                    int ok;
                    ed_y = H - 1; ed_x = 13; ed_w = W - 14;
                    fill(H - 1, 0, W, AN);
                    putsn(H - 1, 0, "SEARCH for:", 12, AT);
                    ok = edit_line(t, sizeof t, -1, &hgen, NULL, bg_prompt);
                    if (!ok || !t[0]) break;
                }
                scopy(search, t, sizeof search);
                found = -1;
            }
            from = hex ? (long long)top * 16 : lines[top];
            if (found >= from) from = found + 1;
            p = memfind(data + from, len - from, search, strlen(search));
            if (!p) { beep(); found = -1; break; }
            found = p - data;
            if (hex) top = found / 16;
            else {
                long lo = 0, hi = nlines - 1;
                while (lo < hi) { long m = (lo + hi + 1) / 2; if (lines[m] <= found) lo = m; else hi = m - 1; }
                top = lo;
            }
            break;
        }
        }
    }
    free(data);
    free(lines);
}

/* ------------------------------------------------------------------ */
/* file operations                                                     */
/* ------------------------------------------------------------------ */

static int overwrite_all;

/* returns 0 ok, 1 skipped, -1 error (message shown), -2 abort */
static int copy_one(const char *src, const char *dst_in, char *dst_out, size_t dn)
{
    struct stat ss, ds;
    char dst[MAXP];
    int in, out;
    char *buf;
    ssize_t n;
    struct utimbuf ut;

    if (lstat(src, &ss) < 0) { msg("%s: %s", src, strerror(errno)); return -1; }
    scopy(dst, dst_in, sizeof dst);
    if (stat(dst, &ds) == 0 && S_ISDIR(ds.st_mode)) join_path(dst, sizeof dst, dst_in, base_name(src));
    if (dst_out) scopy(dst_out, dst, dn);
    if (lstat(dst, &ds) == 0) {
        if (ds.st_dev == ss.st_dev && ds.st_ino == ss.st_ino) { msg("Can't copy %s onto itself", src); return -1; }
        if (!overwrite_all) {
            char q[MAXP];
            int a;
            snprintf(q, sizeof q, "%s exists.  Overwrite?  Yes  No  All", dst);
            a = ask("FILE EXISTS", q, "yna");
            if (!a) return -2;
            if (a == 'n') return 1;
            if (a == 'a') overwrite_all = 1;
        }
        unlink(dst);
    }
    if (S_ISLNK(ss.st_mode)) {
        char lt[MAXP];
        int l = readlink(src, lt, sizeof lt - 1);
        if (l < 0 || (lt[l] = 0, symlink(lt, dst) < 0)) { msg("%s: %s", dst, strerror(errno)); return -1; }
        return 0;
    }
    if (!S_ISREG(ss.st_mode)) { msg("%s: not a regular file, skipped", src); return 1; }
    in = open(src, O_RDONLY);
    if (in < 0) { msg("%s: %s", src, strerror(errno)); return -1; }
    out = open(dst, O_WRONLY | O_CREAT | O_TRUNC, ss.st_mode & 07777);
    if (out < 0) { msg("%s: %s", dst, strerror(errno)); close(in); return -1; }
    buf = xmalloc(65536);
    while ((n = read(in, buf, 65536)) > 0) {
        char *p = buf;
        while (n > 0) {
            ssize_t w = write(out, p, n);
            if (w < 0) {
                if (errno == EINTR) continue;
                msg("%s: %s", dst, strerror(errno));
                free(buf); close(in); close(out);
                return -1;
            }
            p += w; n -= w;
        }
    }
    free(buf);
    close(in);
    if (close(out) < 0) { msg("%s: %s", dst, strerror(errno)); return -1; }
    ut.actime = ss.st_atime;
    ut.modtime = ss.st_mtime;
    utime(dst, &ut);
    return 0;
}

static int move_one(const char *src, const char *dst_in, char *dst_out, size_t dn)
{
    struct stat ds;
    char dst[MAXP];
    int r;
    scopy(dst, dst_in, sizeof dst);
    if (stat(dst, &ds) == 0 && S_ISDIR(ds.st_mode)) join_path(dst, sizeof dst, dst_in, base_name(src));
    if (dst_out) scopy(dst_out, dst, dn);
    if (lstat(dst, &ds) == 0 && !overwrite_all) {
        char q[MAXP];
        int a;
        snprintf(q, sizeof q, "%s exists.  Overwrite?  Yes  No  All", dst);
        a = ask("FILE EXISTS", q, "yna");
        if (!a) return -2;
        if (a == 'n') return 1;
        if (a == 'a') overwrite_all = 1;
    }
    if (rename(src, dst) == 0) return 0;
    if (errno != EXDEV) { msg("%s: %s", src, strerror(errno)); return -1; }
    r = copy_one(src, dst, NULL, 0);
    if (r == 0 && unlink(src) < 0) { msg("%s: %s", src, strerror(errno)); return -1; }
    return r;
}

/* collect the paths of the files an operation applies to */
static char **op_targets(Pane *p, int tagged, int *n)
{
    char **v;
    int i, k = 0;
    if (lists_dirty) rebuild_lists();
    *n = 0;
    if (!tagged) {
        FileEnt *f = cur_file(p);
        if (!f) return NULL;
        v = xmalloc(sizeof *v);
        {
            char b[MAXP];
            file_path(f, b, sizeof b);
            v[0] = xstrdup(b);
        }
        *n = 1;
        return v;
    }
    for (i = 0; i < p->nfl; i++) if (p->fl[i]->tagged) k++;
    if (!k) return NULL;
    v = xmalloc(k * sizeof *v);
    for (i = 0; i < p->nfl; i++)
        if (p->fl[i]->tagged) {
            char b[MAXP];
            file_path(p->fl[i], b, sizeof b);
            v[(*n)++] = xstrdup(b);
        }
    return v;
}

static void free_targets(char **v, int n)
{
    int i;
    for (i = 0; i < n; i++) free(v[i]);
    free(v);
}

static char last_dest[MAXP] = "";

static void op_copy_move(Pane *p, int tagged, int move)
{
    int n, i, done = 0;
    char **v = op_targets(p, tagged, &n);
    char title[MAXP], dest[MAXP], full[MAXP], base[MAXP], out[MAXP];
    if (!v) { msg(tagged ? "No tagged files" : "No file"); return; }
    if (npanes == 2) dir_path(P[1 - ap].cur, dest, sizeof dest);
    else if (last_dest[0]) scopy(dest, last_dest, sizeof dest);
    else dir_path(p->cur, dest, sizeof dest);
    if (tagged) snprintf(title, sizeof title, "%s all %d tagged files", move ? "MOVE" : "COPY", n);
    else snprintf(title, sizeof title, "%s file: %s", move ? "MOVE" : "COPY", v[0]);
    scopy(base, v[0], sizeof base);
    *strrchr(base, '/') = 0;
    if (!base[0]) strcpy(base, "/");
    if (!prompt(title, "to:", dest, sizeof dest, NULL, base) || !dest[0]) { free_targets(v, n); return; }
    expand_path(dest, base, full, sizeof full);
    scopy(last_dest, full, sizeof last_dest);
    if (n > 1) {
        struct stat st;
        if (stat(full, &st) < 0 || !S_ISDIR(st.st_mode)) {
            msg("%s is not a directory", full);
            free_targets(v, n);
            return;
        }
    }
    overwrite_all = 0;
    for (i = 0; i < n; i++) {
        int r;
        status("%s %s", move ? "Moving" : "Copying", v[i]);
        r = move ? move_one(v[i], full, out, sizeof out) : copy_one(v[i], full, out, sizeof out);
        if (r == -2) break;
        if (r == 0) {
            done++;
            relog_parent_of(out);
            if (move) relog_parent_of(v[i]);
        }
        if (esc_pressed()) break;
    }
    free_targets(v, n);
    status("%d file(s) %s", done, move ? "moved" : "copied");
}

static void op_delete(Pane *p, int tagged)
{
    int n, i, each = 1, done = 0;
    char **v = op_targets(p, tagged, &n);
    char q[MAXP];
    if (!v) { msg(tagged ? "No tagged files" : "No file"); return; }
    if (tagged) {
        int a;
        snprintf(q, sizeof q, "Delete all %d tagged files?  Yes  No", n);
        if (ask("DELETE tagged files", q, "yn") != 'y') { free_targets(v, n); return; }
        a = ask("DELETE tagged files", "Confirm each file?  Yes  No", "yn");
        if (!a) { free_targets(v, n); return; }
        each = (a == 'y');
    }
    for (i = 0; i < n; i++) {
        if (each) {
            int a;
            snprintf(q, sizeof q, "Delete %s ?  Yes  No", v[i]);
            a = ask("DELETE file", q, "yn");
            if (!a) break;
            if (a == 'n') continue;
        }
        if (unlink(v[i]) < 0) msg("%s: %s", v[i], strerror(errno));
        else { done++; relog_parent_of(v[i]); }
    }
    free_targets(v, n);
    if (done) status("%d file(s) deleted", done);
}

static void op_rename(Pane *p)
{
    FileEnt *f = cur_file(p);
    char old[MAXP], nn[256], np[MAXP], dir[MAXP], title[MAXP];
    if (!f) return;
    file_path(f, old, sizeof old);
    dir_path(f->dir, dir, sizeof dir);
    scopy(nn, f->name, sizeof nn);
    snprintf(title, sizeof title, "RENAME file: %s", old);
    if (!prompt(title, "as:", nn, sizeof nn, NULL, dir) || !nn[0]) return;
    if (strchr(nn, '/')) { msg("Use Move to put a file in another directory"); return; }
    join_path(np, sizeof np, dir, nn);
    if (access(np, F_OK) == 0) { msg("%s already exists", np); return; }
    if (rename(old, np) < 0) { msg("%s: %s", old, strerror(errno)); return; }
    log_dir(f->dir);
    scopy(p->selname, nn, sizeof p->selname);
}

static void op_attr(Pane *p, int tagged)
{
    int n, i;
    char **v = op_targets(p, tagged, &n);
    char m[64] = "", title[MAXP], cmd[MAXP * 2], q[MAXP];
    if (!v) { msg(tagged ? "No tagged files" : "No file"); return; }
    if (!tagged) {
        struct stat st;
        if (lstat(v[0], &st) == 0) sprintf(m, "%o", (unsigned)(st.st_mode & 07777));
        snprintf(title, sizeof title, "ATTRIBUTES for %s", v[0]);
    } else snprintf(title, sizeof title, "ATTRIBUTES for %d tagged files", n);
    if (!prompt(title, "mode (e.g. 644, +x, go-w):", m, sizeof m, NULL, NULL) || !m[0]) { free_targets(v, n); return; }
    for (i = 0; i < n; i++) {
        char *end;
        long om = strtol(m, &end, 8);
        if (*end == 0 && om >= 0 && om <= 07777) {
            if (chmod(v[i], (mode_t)om) < 0) msg("%s: %s", v[i], strerror(errno));
        } else {
            int st;
            shquote(v[i], q, sizeof q);
            snprintf(cmd, sizeof cmd, "chmod -- %s %s >/dev/null 2>&1", m, q);
            st = system(cmd);
            if (st != 0) { msg("chmod %s failed for %s", m, v[i]); }
        }
        relog_parent_of(v[i]);
    }
    free_targets(v, n);
}

static void op_touch(Pane *p, int tagged)
{
    int n, i;
    char **v = op_targets(p, tagged, &n);
    if (!v) { msg(tagged ? "No tagged files" : "No file"); return; }
    for (i = 0; i < n; i++) {
        if (utime(v[i], NULL) < 0) msg("%s: %s", v[i], strerror(errno));
        relog_parent_of(v[i]);
    }
    free_targets(v, n);
}

static void op_edit(Pane *p)
{
    FileEnt *f = cur_file(p);
    char path[MAXP], q[MAXP], cmd[MAXP * 2], dir[MAXP];
    const char *ed = getenv("VISUAL");
    if (!f) return;
    if (!ed || !*ed) ed = getenv("EDITOR");
    if (!ed || !*ed) ed = access("/usr/bin/nano", X_OK) == 0 ? "nano" : "vi";
    file_path(f, path, sizeof path);
    dir_path(f->dir, dir, sizeof dir);
    shquote(path, q, sizeof q);
    snprintf(cmd, sizeof cmd, "%s %s", ed, q);
    run_shell(dir, cmd, 0);
    log_dir(f->dir);
}

static void op_open(Pane *p)
{
    FileEnt *f = cur_file(p);
    char path[MAXP];
    if (!f) return;
    file_path(f, path, sizeof path);
    if (!getenv("DISPLAY")) { msg("Open needs X (DISPLAY is not set); try View or Edit"); return; }
    spawn_detached("xdg-open", path);
    status("Opening %s", path);
}

/* ------------------------------------------------------------------ */
/* directory operations                                                */
/* ------------------------------------------------------------------ */

static void set_cur(Pane *p, Dir *d)
{
    p->cur = d;
    p->fsel = 0;
    p->ftop = 0;
    p->selname[0] = 0;
    mark_lists();
    lists_dirty = 1;
}

static void dop_make(Pane *p)
{
    char path[MAXP], name[256] = "", np[MAXP], title[MAXP];
    dir_path(p->cur, path, sizeof path);
    snprintf(title, sizeof title, "MAKE DIRECTORY under: %s", path);
    if (!prompt(title, "as:", name, sizeof name, NULL, path) || !name[0]) return;
    expand_path(name, path, np, sizeof np);
    if (mkdir(np, 0777) < 0) { msg("%s: %s", np, strerror(errno)); return; }
    relog_parent_of(np);
    p->cur->expanded = 1;
}

static void dop_delete(Pane *p)
{
    char path[MAXP], q[MAXP];
    Dir *par = p->cur->parent;
    if (!par) { msg("Can't delete the root directory"); return; }
    dir_path(p->cur, path, sizeof path);
    snprintf(q, sizeof q, "Delete directory %s ?  Yes  No", path);
    if (ask("DELETE directory", q, "yn") != 'y') return;
    if (rmdir(path) < 0) {
        if (errno == ENOTEMPTY || errno == EEXIST) msg("Directory not empty.  Alt+P prunes a whole branch.");
        else msg("%s: %s", path, strerror(errno));
        return;
    }
    set_cur(p, par);
    log_dir(par);
}

static int prune_cb(const char *path, const struct stat *sb, int flag, struct FTW *ftw)
{
    (void)sb; (void)ftw;
    if (flag == FTW_DP || flag == FTW_D) return rmdir(path) < 0 ? 0 : 0;
    unlink(path);
    return 0;
}

static void dop_prune(Pane *p)
{
    char path[MAXP], q[MAXP], ans[16] = "";
    Dir *par = p->cur->parent;
    if (!par) { msg("Can't prune the root directory"); return; }
    dir_path(p->cur, path, sizeof path);
    snprintf(q, sizeof q, "PRUNE: delete %s and EVERYTHING under it.  Type YES to confirm", path);
    if (!prompt(q, "", ans, sizeof ans, NULL, NULL)) return;
    if (strcmp(ans, "YES") && strcmp(ans, "yes")) return;
    status("Pruning %s ...", path);
    nftw(path, prune_cb, 32, FTW_DEPTH | FTW_PHYS | FTW_MOUNT);
    set_cur(p, par);
    log_dir(par);
    if (access(path, F_OK) == 0) msg("Some files under %s could not be removed", path);
}

static void dop_rename(Pane *p)
{
    char path[MAXP], ppath[MAXP], name[256], np[MAXP], title[MAXP];
    Dir *par = p->cur->parent, *k;
    if (!par) { msg("Can't rename the root directory"); return; }
    dir_path(p->cur, path, sizeof path);
    dir_path(par, ppath, sizeof ppath);
    scopy(name, p->cur->name, sizeof name);
    snprintf(title, sizeof title, "RENAME directory: %s", path);
    if (!prompt(title, "as:", name, sizeof name, NULL, ppath) || !name[0]) return;
    if (strchr(name, '/')) { msg("New name can't contain '/'"); return; }
    join_path(np, sizeof np, ppath, name);
    if (rename(path, np) < 0) { msg("%s: %s", path, strerror(errno)); return; }
    log_dir(par);
    k = find_kid(par, name);
    set_cur(p, k ? k : par);
}

static void tag_dir(Dir *d, int how, int recurse)  /* how: 1 tag 0 untag 2 invert */
{
    int i;
    for (i = 0; i < d->nfiles; i++)
        if (matches(d->files[i].name))
            d->files[i].tagged = how == 2 ? !d->files[i].tagged : how;
    if (recurse) for (i = 0; i < d->nkids; i++) tag_dir(d->kids[i], how, 1);
    stats_dirty = 1;
    mark_lists();
}

/* filesystems never logged automatically (virtual, or network ones that can hang) */
static const char *skip_fs[] = {
    "proc", "sysfs", "devpts", "devtmpfs", "cgroup", "cgroup2", "securityfs", "debugfs",
    "tracefs", "pstore", "bpf", "mqueue", "hugetlbfs", "configfs", "fusectl", "binfmt_misc",
    "autofs", "efivarfs", "usbfs", "usbdevfs", "rpc_pipefs", "nfsd", "selinuxfs", "devfs",
    "nfs", "nfs4", "smbfs", "cifs", "ncpfs", "coda", "afs", "sshfs", "fuse.sshfs", "fuse.gvfsd-fuse",
    NULL
};

static char **skip_mnt;
static int nskip_mnt;

static void load_skip_mounts(void)
{
    FILE *f = fopen("/proc/mounts", "r");
    char line[1024], d[512], m[512], t[64];
    int i;
    for (i = 0; i < nskip_mnt; i++) free(skip_mnt[i]);
    nskip_mnt = 0;
    if (!f) return;
    while (fgets(line, sizeof line, f)) {
        if (sscanf(line, "%511s %511s %63s", d, m, t) != 3) continue;
        unescape_mnt(m);
        for (i = 0; skip_fs[i]; i++)
            if (!strcmp(t, skip_fs[i])) {
                skip_mnt = xrealloc(skip_mnt, (nskip_mnt + 1) * sizeof *skip_mnt);
                skip_mnt[nskip_mnt++] = xstrdup(m);
                break;
            }
    }
    fclose(f);
}

static int skip_dir(Dir *d)
{
    char b[MAXP];
    int i;
    if (!d->parent || d->dev == d->parent->dev) return 0;   /* not a mount point */
    dir_path(d, b, sizeof b);
    for (i = 0; i < nskip_mnt; i++) if (!strcmp(b, skip_mnt[i])) return 1;
    return 0;
}

typedef struct {
    long dirs, files;
    long long total;     /* estimate from used inodes, 0 = unknown */
    int abort_, expand, box;
    time_t last;
} LogJob;

static void progress_box(LogJob *j, Dir *d)
{
    char b[MAXP], n1[32], n2[32], line[128];
    int bw = W - 10, bx, by, barw, fillw, pct = -1, i;
    if (bw > 64) bw = 64;
    bx = (W - bw) / 2;
    by = (H - 8) / 2;
    erase();
    putsn(0, 1, "Path: /", 7, AN);
    draw_clock();
    for (i = 0; i < 8; i++) fill(by + i, bx, bw, AN);
    attrset(AN);
    mvaddch(by, bx, ACS_ULCORNER); mvhline(by, bx + 1, ACS_HLINE, bw - 2); mvaddch(by, bx + bw - 1, ACS_URCORNER);
    mvvline(by + 1, bx, ACS_VLINE, 6); mvvline(by + 1, bx + bw - 1, ACS_VLINE, 6);
    mvaddch(by + 7, bx, ACS_LLCORNER); mvhline(by + 7, bx + 1, ACS_HLINE, bw - 2); mvaddch(by + 7, bx + bw - 1, ACS_LRCORNER);
    putsn(by, bx + 2, " Logging disk ", 14, AT);
    barw = bw - 12;
    if (j->total > 0) {
        pct = (int)((j->dirs + j->files) * 100 / j->total);
        if (pct > 99) pct = 99;
    }
    fillw = pct >= 0 ? barw * pct / 100 : 0;
    fill(by + 2, bx + 3, fillw, AB);
    attrset(AD);
    for (i = fillw; i < barw; i++) mvaddch(by + 2, bx + 3 + i, ACS_CKBOARD);
    if (pct >= 0) { sprintf(line, "%3d%%", pct); putsn(by + 2, bx + 4 + barw, line, 4, AN); }
    commas(j->dirs, n1);
    commas(j->files, n2);
    sprintf(line, "Directories %s    Files %s", n1, n2);
    putsn(by + 4, bx + 3, line, bw - 6, AN);
    dir_path(d, b, sizeof b);
    putstail(by + 5, bx + 3, b, bw - 6, AD);
    putsn(by + 6, bx + bw - 22, "ESC skips the rest", 18, AD);
    cmd_overlay(NULL, NULL, NULL);
    refresh();
}

static void log_all(Dir *d, LogJob *j)
{
    int i;
    if (j->abort_) return;
    if (!d->logged) log_dir(d);
    if (j->expand) d->expanded = 1;
    j->dirs++;
    j->files += d->nfiles;
    if (j->dirs % 20 == 0 && time(NULL) != j->last) {
        j->last = time(NULL);
        if (j->box) progress_box(j, d);
        else {
            char b[MAXP];
            dir_path(d, b, sizeof b);
            status("Logging %ld directories ... %s   (ESC stops)", j->dirs, b);
        }
        if (esc_pressed()) { j->abort_ = 1; return; }
    }
    for (i = 0; i < d->nkids; i++)
        if (!skip_dir(d->kids[i])) log_all(d->kids[i], j);
}

static void log_everything(Dir *start, int box, int expand)
{
    LogJob j;
    struct statvfs sv;
    memset(&j, 0, sizeof j);
    j.box = box;
    j.expand = expand;
    load_skip_mounts();
    {
        /* rough total from used inodes on the real filesystems we will visit */
        FILE *f = fopen("/proc/mounts", "r");
        char line[1024], dv[512], m[512], t[64], sp[MAXP];
        dir_path(start, sp, sizeof sp);
        if (f) {
            while (fgets(line, sizeof line, f)) {
                int k, skip = 0;
                size_t l;
                if (sscanf(line, "%511s %511s %63s", dv, m, t) != 3) continue;
                unescape_mnt(m);
                if (!strcmp(t, "rootfs")) continue;
                for (k = 0; skip_fs[k]; k++) if (!strcmp(t, skip_fs[k])) skip = 1;
                l = strlen(sp);
                if (skip || !(strcmp(sp, "/") == 0 || (strncmp(m, sp, l) == 0 && (m[l] == 0 || m[l] == '/'))))
                    continue;
                if (statvfs(m, &sv) == 0 && sv.f_files > sv.f_ffree)
                    j.total += (long long)(sv.f_files - sv.f_ffree);
            }
            fclose(f);
        }
    }
    j.last = 0;
    if (box) progress_box(&j, start);
    log_all(start, &j);
}

static void dop_compare(Pane *p)
{
    char path[MAXP], other[MAXP] = "", full[MAXP], title[MAXP], t[MAXP];
    int a, i, ntag = 0;
    struct stat st;
    dir_path(p->cur, path, sizeof path);
    if (npanes == 2) dir_path(P[1 - ap].cur, other, sizeof other);
    snprintf(title, sizeof title, "COMPARE %s", path);
    if (!prompt(title, "with directory:", other, sizeof other, NULL, path) || !other[0]) return;
    expand_path(other, path, full, sizeof full);
    if (stat(full, &st) < 0 || !S_ISDIR(st.st_mode)) { msg("%s is not a directory", full); return; }
    a = ask("COMPARE: tag files that are", "Unique  Newer  Both (unique or newer)  Identical  Older", "unbio");
    if (!a) return;
    for (i = 0; i < p->cur->nfiles; i++) {
        FileEnt *f = &p->cur->files[i];
        int exists, tag = 0;
        if (!matches(f->name)) continue;
        join_path(t, sizeof t, full, f->name);
        exists = lstat(t, &st) == 0;
        switch (a) {
        case 'u': tag = !exists; break;
        case 'n': tag = exists && f->mtime > st.st_mtime; break;
        case 'b': tag = !exists || f->mtime > st.st_mtime; break;
        case 'i': tag = exists && f->mtime == st.st_mtime && f->size == st.st_size; break;
        case 'o': tag = exists && f->mtime < st.st_mtime; break;
        }
        f->tagged = tag;
        ntag += tag;
    }
    stats_dirty = 1;
    mark_lists();
    msg("%d file(s) tagged", ntag);
}

static void print_tree(FILE *f, Dir *d, int depth)
{
    int i;
    for (i = 0; i < depth; i++) fputs("    ", f);
    fprintf(f, "%s%s\n", depth ? d->name : "/", d->logged ? "" : "  (not logged)");
    if (d->expanded) for (i = 0; i < d->nkids; i++) print_tree(f, d->kids[i], depth + 1);
}

static void op_print(Pane *p)
{
    char out[MAXP], full[MAXP], b[MAXP], sz[32], dt[32], md[16];
    const char *h = getenv("HOME");
    FILE *f;
    int i;
    snprintf(out, sizeof out, "%s/tta_print.txt", h ? h : "/tmp");
    if (!prompt(p->fmode ? "PRINT file list to file" : "PRINT directory tree to file", "file:",
                out, sizeof out, NULL, h ? h : "/"))
        return;
    expand_path(out, h ? h : "/", full, sizeof full);
    f = fopen(full, "w");
    if (!f) { msg("%s: %s", full, strerror(errno)); return; }
    if (!p->fmode) print_tree(f, root, 0);
    else {
        if (lists_dirty) rebuild_lists();
        for (i = 0; i < p->nfl; i++) {
            FileEnt *e = p->fl[i];
            file_path(e, b, sizeof b);
            commas((long long)e->size, sz);
            fmt_date_short(e->mtime, dt);
            lsmode(e->mode, md);
            fprintf(f, "%c %s %15s  %s  %s\n", e->tagged ? '*' : ' ', md, sz, dt, b);
        }
    }
    fclose(f);
    relog_parent_of(full);
    msg("Written to %s", full);
}

/* ------------------------------------------------------------------ */
/* stats, help, menus                                                  */
/* ------------------------------------------------------------------ */

static void show_stats(void)
{
    static char lines[24][128];
    const char *lp[24];
    char a[48], b[48], c[48];
    char path[MAXP];
    long long fm = free_memory();
    int n = 0, i;
    if (stats_dirty) compute_stats();
    dir_path(P[ap].cur, path, sizeof path);
    update_disk(path);
    sprintf(lines[n++], "Directories logged   %ld", ST.dirs);
    commas(ST.files, a); commas(ST.bytes, b);
    sprintf(lines[n++], "Total files          %-14s %s bytes", a, b);
    commas(ST.mfiles, a); commas(ST.mbytes, b);
    sprintf(lines[n++], "Matching files       %-14s %s bytes   (filespec: %.40s)", a, b, specstr);
    commas(ST.tfiles, a); commas(ST.tbytes, b);
    sprintf(lines[n++], "Tagged files         %-14s %s bytes", a, b);
    lines[n++][0] = 0;
    snprintf(lines[n++], 128, "Disk                 %.60s", DK.dev);
    snprintf(lines[n++], 128, "Mounted on           %.60s", DK.mnt);
    snprintf(lines[n++], 128, "Filesystem type      %.60s", DK.type);
    if (DK.total >= 0) {
        human((double)DK.total, a);
        human((double)DK.avail, b);
        commas(DK.avail, c);
        sprintf(lines[n++], "Size                 %s", a);
        sprintf(lines[n++], "Available            %s  (%s bytes)", b, c);
    }
    lines[n++][0] = 0;
    if (fm >= 0) { human((double)fm, a); sprintf(lines[n++], "Free memory          %s", a); }
    sprintf(lines[n++], "Sort order           %s", sortnames[sortmode]);
    for (i = 0; i < n; i++) lp[i] = lines[i];
    text_screen("TTreeAu Statistics", lp, n);
}

static const char *help_lines[] = {
    "{TTreeAu for Linux} - keys",
    "",
    "{TREE WINDOW}",
    "  {Up/Down PgUp/PgDn Home/End}  move through the directory tree",
    "  {Right} or {+}      expand the highlighted directory (reads it if needed)",
    "  {Left} or {-}       collapse it; on a collapsed directory go to its parent",
    "  {*}                 read and expand the whole branch (skips /proc, /sys, network mounts)",
    "  {Enter}             go to the file window",
    "  {A}vail   show free space on the highlighted directory's disk",
    "  {B}ranch  show every file in the highlighted branch      ({Ctrl+B}: tagged only)",
    "  {C}ompare tag files by comparing with another directory",
    "  {D}elete  remove the highlighted (empty) directory       ({Alt+P}: prune branch)",
    "  {F}ilespec  e.g.  *.c *.h   or   * -*.o   ('-' excludes)",
    "  {Alt+F}     file display: names / +permissions / +size, permissions, date, time",
    "  {G}lobal / {S}howall  show every logged file               ({Ctrl+S}: tagged only)",
    "  {I}nvert  invert tags      {T}ag / {U}ntag  tag/untag files here",
    "  {Ctrl+T} / {Ctrl+U}  tag / untag every file in the branch",
    "  {L}og     re-read the highlighted directory and everything already read under it",
    "            (use after mounting something, or creating files outside TTreeAu)",
    "  {M}ake    make a directory        {R}ename  rename the directory",
    "  {P}rint   write the tree or file list to a text file",
    "  {V}olume  show device, mount point and filesystem type",
    "  e{X}ecute run a shell command in the highlighted directory",
    "  {Q}uit    quit         {Alt+Q}  quit into the highlighted directory (see README)",
    "",
    "{FILE WINDOW}",
    "  arrows move; Left/Right jump a column        {Space} tag and move down",
    "  {A}ttributes (chmod)  {C}opy  {D}elete  {M}ove  {N}ew date (touch)",
    "  {E}dit ($EDITOR)  {O}pen (xdg-open, under X)  {R}ename  {V}iew  e{X}ecute",
    "  {T}ag / {U}ntag  {I}nvert  {F}ilespec  {Alt+F} file display  {L}og  {P}rint",
    "  {Shift} + A C D M N T U (or {Ctrl} + A C D N T U) act on all tagged files",
    "  {Alt+S}  change sort order",
    "  {Enter} or {ESC}  back to the tree",
    "",
    "{EVERYWHERE}",
    "  {F1} help   {F7} autoview   {F8} split screen ({Tab} switches side)",
    "  {F9} application menu (~/.ttamenu)   {F10} command menu   {?} statistics",
    "  {Alt+V} or {F12}  show version and copyright",
    "  {Ctrl+L}  redraw the screen",
    "",
    "{VIEW}  arrows/PgUp/PgDn scroll, Left/Right pan, H hex, / search, N next",
    "",
    "Prompts: Up/Down recall history, Tab completes file names, Ctrl+U clears.",
};

typedef struct { const char *label; int key; } MenuItem;

static const MenuItem tree_menu[] = {
    { "Avail - free disk space            A", 'a' },
    { "Branch - all files in branch       B", 'b' },
    { "Branch - tagged files in branch    Ctrl+B", CTL('b') },
    { "Compare directories                C", 'c' },
    { "Delete empty directory             D", 'd' },
    { "Prune - delete whole branch        Alt+P", ALT('p') },
    { "Filespec (e.g. *.c *.h)            F", 'f' },
    { "File display: names/perms/details  Alt+F", ALT('f') },
    { "Global / Showall - all files       S", 's' },
    { "Showall - tagged files             Ctrl+S", CTL('s') },
    { "Invert tags                        I", 'i' },
    { "Log - refresh directory            L", 'l' },
    { "Log whole branch                   *", '*' },
    { "Make directory                     M", 'm' },
    { "Print tree to file                 P", 'p' },
    { "Rename directory                   R", 'r' },
    { "Tag files                          T", 't' },
    { "Tag all files in branch            Ctrl+T", CTL('t') },
    { "Untag files                        U", 'u' },
    { "Untag all files in branch          Ctrl+U", CTL('u') },
    { "Volume information                 V", 'v' },
    { "eXecute a command                  X", 'x' },
    { "Autoview                           F7", K_F(7) },
    { "Split / unsplit                    F8", K_F(8) },
    { "Application menu                   F9", K_F(9) },
    { "Statistics                         ?", '?' },
    { "Help                               F1", K_F(1) },
    { "Version / copyright                Alt+V", ALT('v') },
    { "Quit                               Q", 'q' },
    { "Quit to this directory             Alt+Q", ALT('q') },
};

static const MenuItem file_menu[] = {
    { "Attributes (chmod)                 A", 'a' },
    { "Attributes of tagged files         Shift+A", 'A' },
    { "Copy                               C", 'c' },
    { "Copy tagged files                  Shift+C", 'C' },
    { "Delete                             D", 'd' },
    { "Delete tagged files                Shift+D", 'D' },
    { "Edit                               E", 'e' },
    { "Invert tags                        I", 'i' },
    { "Log - refresh                      L", 'l' },
    { "Move                               M", 'm' },
    { "Move tagged files                  Shift+M", 'M' },
    { "New date (touch)                   N", 'n' },
    { "New date of tagged files           Shift+N", 'N' },
    { "Open with desktop application      O", 'o' },
    { "Print file list to file            P", 'p' },
    { "Rename                             R", 'r' },
    { "Tag file                           T", 't' },
    { "Tag all files                      Shift+T", 'T' },
    { "Untag file                         U", 'u' },
    { "Untag all files                    Shift+U", 'U' },
    { "View                               V", 'v' },
    { "eXecute a command                  X", 'x' },
    { "Filespec (e.g. *.c *.h)            F", 'f' },
    { "File display: names/perms/details  Alt+F", ALT('f') },
    { "Change sort order                  Alt+S", ALT('s') },
    { "Autoview                           F7", K_F(7) },
    { "Split / unsplit                    F8", K_F(8) },
    { "Application menu                   F9", K_F(9) },
    { "Statistics                         ?", '?' },
    { "Help                               F1", K_F(1) },
    { "Back to tree                       Enter", '\n' },
    { "Quit                               Q", 'q' },
};

static int command_menu(int filemode)
{
    const MenuItem *m = filemode ? file_menu : tree_menu;
    int n = filemode ? (int)(sizeof file_menu / sizeof *m) : (int)(sizeof tree_menu / sizeof *m);
    char **items = xmalloc(n * sizeof *items);
    int i, r;
    for (i = 0; i < n; i++) items[i] = (char *)m[i].label;
    r = popup(filemode ? "FILE COMMANDS" : "DIR COMMANDS", items, n, 0);
    free(items);
    return r < 0 ? 0 : m[r].key;
}

static const char *default_menu =
    "# TTreeAu application menu (F9).  One entry per line:\n"
    "#     Label | shell command\n"
    "# %f = highlighted file (full path)   %n = file name   %d = directory\n"
    "# (all are shell-quoted for you).  Lines starting with # are ignored.\n"
    "Shell in this directory          | cd %d && exec ${SHELL:-/bin/sh}\n"
    "Disk usage of this directory     | du -sh %d\n"
    "Long listing                     | ls -la %d | ${PAGER:-more}\n"
    "Free disk space                  | df -h\n"
    "File type of highlighted file    | file %f\n"
    "Unpack tar.gz here               | cd %d && tar xzvf %f\n"
    "Edit this menu                   | ${EDITOR:-vi} ~/.ttamenu\n";

static void subst_cmd(const char *tmpl, const char *fpath, const char *fname, const char *dir,
                      char *out, size_t n)
{
    size_t j = 0;
    char q[MAXP];
    for (; *tmpl && j + 1 < n; tmpl++) {
        if (*tmpl == '%' && tmpl[1]) {
            const char *v = NULL;
            switch (tmpl[1]) {
            case 'f': v = fpath; break;
            case 'n': v = fname; break;
            case 'd': v = dir; break;
            case '%': out[j++] = '%'; tmpl++; continue;
            }
            if (v) {
                size_t l;
                shquote(v, q, sizeof q);
                l = strlen(q);
                if (j + l >= n) break;
                memcpy(out + j, q, l);
                j += l;
                tmpl++;
                continue;
            }
        }
        out[j++] = *tmpl;
    }
    out[j] = 0;
}

static void app_menu(void)
{
    char path[MAXP], line[MAXP], *labels[100], *cmds[100];
    char dir[MAXP], fpath[MAXP] = "", fname[256] = "", cmd[MAXP * 2];
    const char *h = getenv("HOME");
    FILE *f;
    int n = 0, i, r;
    Pane *p = &P[ap];
    snprintf(path, sizeof path, "%s/.ttamenu", h ? h : "");
    f = fopen(path, "r");
    if (!f) {
        f = fopen(path, "w");
        if (f) { fputs(default_menu, f); fclose(f); }
        f = fopen(path, "r");
        if (!f) { msg("Can't create %s", path); return; }
    }
    while (fgets(line, sizeof line, f) && n < 100) {
        char *bar, *l = line, *e;
        line[strcspn(line, "\n")] = 0;
        while (*l == ' ' || *l == '\t') l++;
        if (!*l || *l == '#') continue;
        bar = strchr(l, '|');
        if (!bar) continue;
        *bar = 0;
        e = bar - 1;
        while (e >= l && (*e == ' ' || *e == '\t')) *e-- = 0;
        bar++;
        while (*bar == ' ') bar++;
        labels[n] = xstrdup(l);
        cmds[n] = xstrdup(bar);
        n++;
    }
    fclose(f);
    if (!n) { msg("No entries in %s", path); return; }
    r = popup("APPLICATION MENU", labels, n, 0);
    if (r >= 0) {
        if (p->fmode && cur_file(p)) {
            file_path(cur_file(p), fpath, sizeof fpath);
            scopy(fname, cur_file(p)->name, sizeof fname);
            dir_path(cur_file(p)->dir, dir, sizeof dir);
        } else dir_path(p->cur, dir, sizeof dir);
        subst_cmd(cmds[r], fpath, fname, dir, cmd, sizeof cmd);
        run_shell(dir, cmd, 1);
        relog_path(dir);
    }
    for (i = 0; i < n; i++) { free(labels[i]); free(cmds[i]); }
}

/* ------------------------------------------------------------------ */
/* key handling                                                        */
/* ------------------------------------------------------------------ */

static void toggle_split(void)
{
    if (npanes == 1) {
        P[1] = P[0];
        P[1].fl = NULL;
        P[1].nfl = P[1].fcap = 0;
        P[1].fmode = 0;
        P[1].lmode = 0;
        P[1].tagonly = 0;
        npanes = 2;
        ap = 1;
    } else {
        if (ap == 1) {
            free(P[0].fl);
            P[0] = P[1];
        } else free(P[1].fl);
        P[1].fl = NULL;
        npanes = 1;
        ap = 0;
    }
    mark_lists();
    lists_dirty = 1;
}

static int common_key(int c)
{
    Pane *p = &P[ap];
    char path[MAXP], b[64];
    switch (c) {
    case K_F(1): text_screen("TTreeAu Help", help_lines, sizeof help_lines / sizeof *help_lines); return 1;
    case K_F(8): toggle_split(); return 1;
    case K_F(9): app_menu(); return 1;
    case '?': show_stats(); return 1;
    case ALT('v'): case K_F(12): show_about = 1; about_until = 0; return 1;
    case CTL('l'): clearok(curscr, TRUE); return 1;
    case '\t':
        if (npanes == 2) { ap = 1 - ap; mark_lists(); }
        return 1;
    case ALT('s'):
        sortmode = (sortmode + 1) % 4;
        mark_lists();
        status("Sorted by %s", sortnames[sortmode]);
        napms(400);
        return 1;
    case ALT('f'): case '/':
        fmtmode = (fmtmode + 1) % 3;
        return 1;
    case 'f': case 'F': {
        char s[256];
        scopy(s, specstr, sizeof s);
        if (prompt("FILESPEC: e.g. *.c *.h  (- excludes, e.g. * -*.o)", "filespec:", s, sizeof s, NULL, NULL)) {
            set_specs(s);
            mark_lists();
            stats_dirty = 1;
        }
        return 1;
    }
    case 'x': case 'X': {
        char pre[MAXP] = "";
        FileEnt *f = p->fmode ? cur_file(p) : NULL;
        if (f) {
            char q[MAXP];
            dir_path(f->dir, path, sizeof path);
            shquote(f->name, q, sizeof q);
            snprintf(pre, sizeof pre, " %s", q);
        } else dir_path(p->cur, path, sizeof path);
        do_execute(path, pre);
        return 1;
    }
    case 'q': case 'Q':
        if (ask("QUIT", "Quit TTreeAu?  Yes  No", "yn") == 'y') quit_flag = 1;
        return 1;
    case ALT('q'):
        dir_path(p->fmode && cur_file(p) ? cur_file(p)->dir : p->cur, quit_dir, sizeof quit_dir);
        quit_flag = 1;
        return 1;
    case 'v': case 'V':
        if (p->fmode) return 0;
        dir_path(p->cur, path, sizeof path);
        update_disk(path);
        human((double)DK.total, b);
        msg("VOLUME: %s   type %s   mounted on %s   size %s", DK.dev, DK.type, DK.mnt, b);
        return 1;
    }
    return 0;
}

static void tree_key(int c)
{
    Pane *p = &P[ap];
    int ci;
    char path[MAXP], a[32], b[32];
    if (common_key(c)) return;
    build_vis();
    fix_cur_visible(p);
    ci = vis_index(p->cur);
    switch (c) {
    case KEY_UP: if (ci > 0) set_cur(p, vis[ci - 1]); break;
    case KEY_DOWN: if (ci < nvis - 1) set_cur(p, vis[ci + 1]); break;
    case KEY_PPAGE: {
        int h = H - 6 - (H - 5) / 5 - 1;
        ci -= h > 1 ? h - 1 : 1;
        if (ci < 0) ci = 0;
        set_cur(p, vis[ci]);
        break;
    }
    case KEY_NPAGE: {
        int h = H - 6 - (H - 5) / 5 - 1;
        ci += h > 1 ? h - 1 : 1;
        if (ci > nvis - 1) ci = nvis - 1;
        set_cur(p, vis[ci]);
        break;
    }
    case KEY_HOME: set_cur(p, root); break;
    case KEY_END: set_cur(p, vis[nvis - 1]); break;
    case KEY_RIGHT: case '+':
        if (!p->cur->logged) log_dir(p->cur);
        if (p->cur->expanded && p->cur->nkids && c == KEY_RIGHT) set_cur(p, p->cur->kids[0]);
        else p->cur->expanded = 1;
        break;
    case KEY_LEFT: case '-':
        if (p->cur->expanded && p->cur->nkids) p->cur->expanded = 0;
        else if (p->cur->parent) set_cur(p, p->cur->parent);
        break;
    case '*':
        log_everything(p->cur, 0, 1);
        break;
    case '\n': case '\r': case KEY_ENTER:
        p->fmode = 1; p->lmode = 0; p->tagonly = 0;
        mark_lists();
        break;
    case K_F(7):
        p->fmode = 1; p->lmode = 0; p->tagonly = 0; autoview = 1;
        mark_lists();
        break;
    case 'a': case 'A':
        dir_path(p->cur, path, sizeof path);
        update_disk(path);
        human((double)DK.avail, a);
        human((double)DK.total, b);
        msg("AVAILABLE SPACE on %s (%s): %s free of %s", DK.dev, DK.mnt, a, b);
        break;
    case 'b': case 'B': case CTL('b'):
        log_everything(p->cur, 0, 0);
        p->fmode = 1; p->lmode = 1; p->tagonly = (c == CTL('b')); p->fsel = 0;
        mark_lists();
        break;
    case 's': case 'S': case 'g': case 'G': case CTL('s'):
        p->fmode = 1; p->lmode = 2; p->tagonly = (c == CTL('s')); p->fsel = 0;
        mark_lists();
        break;
    case 'c': case 'C': dop_compare(p); break;
    case 'd': case 'D': dop_delete(p); break;
    case ALT('p'): dop_prune(p); break;
    case 'i': case 'I': tag_dir(p->cur, 2, 0); break;
    case 't': case 'T': tag_dir(p->cur, 1, 0); break;
    case 'u': case 'U': tag_dir(p->cur, 0, 0); break;
    case CTL('t'): tag_dir(p->cur, 1, 1); break;
    case CTL('u'): tag_dir(p->cur, 0, 1); break;
    case 'l': case 'L':
        dir_path(p->cur, path, sizeof path);
        status("Re-reading %s ...", path);
        relog_branch(p->cur);
        p->cur->expanded = 1;
        break;
    case 'm': case 'M': dop_make(p); break;
    case 'o': case 'O': msg("Oops! (undelete) isn't possible on Linux filesystems."); break;
    case 'p': case 'P': op_print(p); break;
    case 'r': case 'R': dop_rename(p); break;
    case K_F(10): {
        int k = command_menu(0);
        if (k) tree_key(k);
        break;
    }
    }
}

static void file_key(int c)
{
    Pane *p = &P[ap];
    FileEnt *f;
    int rows, step;
    if (lists_dirty) rebuild_lists();
    if (common_key(c)) return;
    rows = p->vrows > 0 ? p->vrows : 1;
    step = rows * (p->vcols > 0 ? p->vcols : 1);
    f = cur_file(p);
    switch (c) {
    case KEY_UP: if (p->fsel > 0) p->fsel--; break;
    case KEY_DOWN: if (p->fsel < p->nfl - 1) p->fsel++; break;
    case KEY_LEFT: if (p->vcols > 1) { p->fsel -= rows; if (p->fsel < 0) p->fsel = 0; } break;
    case KEY_RIGHT:
        if (p->vcols > 1) { p->fsel += rows; if (p->fsel > p->nfl - 1) p->fsel = p->nfl - 1; }
        break;
    case KEY_PPAGE: p->fsel -= step; if (p->fsel < 0) p->fsel = 0; break;
    case KEY_NPAGE: p->fsel += step; if (p->fsel > p->nfl - 1) p->fsel = p->nfl - 1; break;
    case KEY_HOME: p->fsel = 0; break;
    case KEY_END: p->fsel = p->nfl - 1; break;
    case 27: case '\n': case '\r': case KEY_ENTER:
        p->fmode = 0; p->lmode = 0; p->tagonly = 0; autoview = 0;
        mark_lists();
        break;
    case K_F(7): autoview = !autoview; break;
    case ' ':
        if (f) { f->tagged = !f->tagged; stats_dirty = 1; if (p->fsel < p->nfl - 1) p->fsel++; }
        break;
    case 't':
        if (f) { f->tagged = 1; stats_dirty = 1; if (p->fsel < p->nfl - 1) p->fsel++; }
        break;
    case 'u':
        if (f) { f->tagged = 0; stats_dirty = 1; if (p->fsel < p->nfl - 1) p->fsel++; }
        break;
    case 'T': case CTL('t'): case 'U': case CTL('u'): case 'i': case 'I': {
        int i, how = (c == 'T' || c == CTL('t')) ? 1 : (c == 'i' || c == 'I') ? 2 : 0;
        for (i = 0; i < p->nfl; i++) p->fl[i]->tagged = how == 2 ? !p->fl[i]->tagged : how;
        stats_dirty = 1;
        if (p->tagonly) mark_lists();
        break;
    }
    case 'a': op_attr(p, 0); break;
    case 'A': case CTL('a'): op_attr(p, 1); break;
    case 'c': op_copy_move(p, 0, 0); break;
    case 'C': case CTL('c'): op_copy_move(p, 1, 0); break;
    case 'd': op_delete(p, 0); break;
    case 'D': case CTL('d'): op_delete(p, 1); break;
    case 'm': op_copy_move(p, 0, 1); break;
    case 'M': op_copy_move(p, 1, 1); break;
    case 'n': op_touch(p, 0); break;
    case 'N': case CTL('n'): op_touch(p, 1); break;
    case 'e': case 'E': op_edit(p); break;
    case 'o': case 'O': op_open(p); break;
    case 'r': case 'R': op_rename(p); break;
    case 'p': case 'P': op_print(p); break;
    case 'v': case 'V':
        if (f) {
            char path[MAXP];
            file_path(f, path, sizeof path);
            view_file(path);
        }
        break;
    case 'l': case 'L':
        if (p->lmode == 0) relog_branch(p->cur);
        else if (f) log_dir(f->dir);
        break;
    case K_F(10): {
        int k = command_menu(1);
        if (k) file_key(k);
        break;
    }
    }
}

/* ------------------------------------------------------------------ */
/* main                                                                */
/* ------------------------------------------------------------------ */

static void load_config(void)
{
    char p[MAXP], line[256], k[64], v[64];
    const char *h = getenv("HOME");
    FILE *f;
    if (!h) return;
    snprintf(p, sizeof p, "%s/.ttarc", h);
    f = fopen(p, "r");
    if (!f) {
        f = fopen(p, "w");
        if (f) {
            fputs("# TTreeAu configuration\n"
                  "# clock = 24   (24 hour time)   or   clock = 12   (am/pm)\n"
                  "clock = 24\n"
                  "# log = all    (read the whole disk at startup, like XTreeGold)\n"
                  "# log = lazy   (read directories as you move onto them)\n"
                  "log = all\n", f);
            fclose(f);
        }
        return;
    }
    while (fgets(line, sizeof line, f)) {
        char *c = strchr(line, '#');
        if (c) *c = 0;
        if (sscanf(line, " %63[^= \t] = %63s", k, v) != 2) continue;
        if (!strcasecmp(k, "clock")) clock24 = atoi(v) != 12;
        else if (!strcasecmp(k, "log")) log_all_at_start = strcasecmp(v, "lazy") != 0;
    }
    fclose(f);
}

static void init_colors(void)
{
    if (has_colors()) {
        start_color();
        init_pair(1, COLOR_CYAN, COLOR_BLUE);
        init_pair(2, COLOR_WHITE, COLOR_BLUE);
        init_pair(3, COLOR_BLACK, COLOR_WHITE);
        init_pair(4, COLOR_YELLOW, COLOR_BLUE);
        init_pair(5, COLOR_RED, COLOR_BLUE);
        init_pair(6, COLOR_WHITE, COLOR_CYAN);
        AN = COLOR_PAIR(1) | A_BOLD;
        AD = COLOR_PAIR(1);
        AH = COLOR_PAIR(2) | A_BOLD;
        AB = COLOR_PAIR(3);
        AT = COLOR_PAIR(4) | A_BOLD;
        AE = COLOR_PAIR(5) | A_BOLD;
        AI = COLOR_PAIR(6);
        bkgdset(' ' | COLOR_PAIR(1));
    } else {
        AN = A_NORMAL;
        AD = A_DIM;
        AH = A_BOLD;
        AB = A_REVERSE;
        AT = A_BOLD;
        AE = A_BOLD;
        AI = A_UNDERLINE;
    }
    (void)AE;
}

int main(int argc, char **argv)
{
    char start[MAXP];
    struct stat st;
    Dir *d;
    int lazy_flag = 0;

    setlocale(LC_ALL, "");
    {
        const char *cs = nl_langinfo(CODESET);
        utf8 = cs && (!strcasecmp(cs, "UTF-8") || !strcasecmp(cs, "utf8"));
    }
    if (argc > 1 && (!strcmp(argv[1], "-h") || !strcmp(argv[1], "--help"))) {
        printf("usage: tta [-l] [directory]\n  -l  don't read the whole disk at startup\n");
        return 0;
    }
    if (argc > 1 && !strcmp(argv[1], "-l")) { lazy_flag = 1; argc--; argv++; }
    if (argc > 1) {
        if (!realpath(argv[1], start)) { perror(argv[1]); return 1; }
    } else if (!getcwd(start, sizeof start)) strcpy(start, "/");

    setenv("ESCDELAY", "50", 0);
    if (!initscr()) { fprintf(stderr, "tta: can't initialise the terminal\n"); return 1; }
    raw();
    noecho();
    nonl();
    keypad(stdscr, TRUE);
    curs_set(0);
    init_colors();
    W = COLS; H = LINES;

    set_specs("*");
    load_config();
    load_exec_history();
    if (lstat("/", &st) < 0) st.st_dev = 0;
    root = new_dir(NULL, "", st.st_dev);
    log_dir(root);
    root->expanded = 1;
    if (log_all_at_start && !lazy_flag) log_everything(root, 1, 1);
    d = goto_path(start);
    d->expanded = 1;
    memset(P, 0, sizeof P);
    P[0].cur = d;
    show_about = 1;
    about_until = time(NULL) + 3;
    mark_lists();
    lists_dirty = 1;

    while (!quit_flag) {
        int c;
        if (show_about && about_until && time(NULL) >= about_until) show_about = 0;
        if (!P[ap].cur->logged) log_dir(P[ap].cur);
        draw_main();
        refresh();
        c = getkey();
        if (c == 0 || c == KEY_RESIZE) continue;
        if (show_about) {
            show_about = 0;
            if (c == ALT('v') || c == K_F(12)) continue;
        }
        if (too_small()) {
            if (c == 'q' || c == 'Q') break;
            continue;
        }
        if (P[ap].fmode) file_key(c);
        else tree_key(c);
    }
    endwin();
    if (quit_dir[0]) {
        const char *cdf = getenv("TTA_CDFILE");
        if (cdf) {
            FILE *f = fopen(cdf, "w");
            if (f) { fprintf(f, "%s\n", quit_dir); fclose(f); }
        } else printf("%s\n", quit_dir);
    }
    return 0;
}
