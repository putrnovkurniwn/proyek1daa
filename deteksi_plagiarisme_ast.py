import csv
import time
import tracemalloc
import random
import string

# ============================================================
# 1. PolynomialHash
# ============================================================
class PolynomialHash:
    BASE = 31
    MOD = 1_000_000_007
    CHAR_MAP = {'F': 1, 'L': 2, 'I': 3, 'A': 4, 'R': 5, 'C': 6, 'O': 7, 'V': 8}

    def __init__(self, base=None, mod=None):
        self.base = base if base is not None else self.BASE
        self.mod = mod if mod is not None else self.MOD

    def char_value(self, c):
        return self.CHAR_MAP.get(c, 0)

    def compute_hash(self, s):
        h = 0
        for c in s:
            h = (h * self.base + self.char_value(c)) % self.mod
        return h

    def compute_power(self, exp):
        result = 1
        b = self.base % self.mod
        e = exp
        while e > 0:
            if e & 1:
                result = (result * b) % self.mod
            b = (b * b) % self.mod
            e >>= 1
        return result

    def roll(self, old_hash, out_char, in_char, power):
        out_val = self.char_value(out_char)
        in_val = self.char_value(in_char)
        new_hash = (old_hash - out_val * power) % self.mod
        new_hash = (new_hash * self.base + in_val) % self.mod
        return new_hash


# ============================================================
# 2. RabinKarp (Iteratif & Rekursif)
# ============================================================
class RabinKarp:
    def __init__(self, ph=None):
        self.ph = ph if ph is not None else PolynomialHash()
        self.comparisons = 0

    def _verify(self, text, pattern, start, m):
        for j in range(m):
            self.comparisons += 1
            if text[start + j] != pattern[j]:
                return False
        return True

    # --- VERSI NON-REKURSIF ---
    def exact_search(self, text, pattern):
        n = len(text)
        m = len(pattern)
        if m == 0 or m > n:
            return []
        ph = self.ph
        pat_hash = ph.compute_hash(pattern)
        win_hash = ph.compute_hash(text[:m])
        power = ph.compute_power(m - 1)
        result = []
        for i in range(n - m + 1):
            if win_hash == pat_hash:
                if self._verify(text, pattern, i, m):
                    result.append(i)
            if i < n - m:
                win_hash = ph.roll(win_hash, text[i], text[i + m], power)
        return result

    # --- VERSI REKURSIF (Poin 3 Asesmen) ---
    def exact_search_recursive(self, text, pattern):
        n = len(text)
        m = len(pattern)
        if m == 0 or m > n:
            return []
        
        ph = self.ph
        pat_hash = ph.compute_hash(pattern)
        win_hash = ph.compute_hash(text[:m])
        power = ph.compute_power(m - 1)
        
        def _search(i, current_hash, results):
            if i > n - m:
                return results
            
            if current_hash == pat_hash:
                if self._verify(text, pattern, i, m):
                    results.append(i)
            
            if i < n - m:
                next_hash = ph.roll(current_hash, text[i], text[i + m], power)
                return _search(i + 1, next_hash, results)
            return results
            
        return _search(0, win_hash, [])

    def _hashes_of_substrings(self, s, L):
        ph = self.ph
        n = len(s)
        if L > n: return {}
        h = ph.compute_hash(s[:L])
        power = ph.compute_power(L - 1)
        d = {}
        if h not in d: d[h] = []
        d[h].append(0)
        for i in range(1, n - L + 1):
            h = ph.roll(h, s[i - 1], s[i + L - 1], power)
            if h not in d: d[h] = []
            d[h].append(i)
        return d

    # --- VERSI REKURSIF BINARY SEARCH (Poin 3 Asesmen) ---
    def longest_common_substring_recursive(self, pattern, text):
        n = len(text)
        m = len(pattern)
        ph = self.ph
        
        def _binary_search(lo, hi, best_len, best_pi, best_ti):
            if lo > hi:
                return best_len, best_pi, best_ti
            
            mid = (lo + hi) // 2
            pat_dict = self._hashes_of_substrings(pattern, mid)
            found = False
            found_pi = -1
            found_ti = -1
            
            if mid <= n:
                h = ph.compute_hash(text[:mid])
                power = ph.compute_power(mid - 1)
                for i in range(n - mid + 1):
                    if h in pat_dict:
                        for pi in pat_dict[h]:
                            ok = True
                            for k in range(mid):
                                self.comparisons += 1
                                if pattern[pi + k] != text[i + k]:
                                    ok = False
                                    break
                            if ok:
                                found = True
                                found_pi = pi
                                found_ti = i
                                break
                    if found: break
                    if i < n - mid:
                        h = ph.roll(h, text[i], text[i + mid], power)
            
            if found:
                return _binary_search(mid + 1, hi, mid, found_pi, found_ti)
            else:
                return _binary_search(lo, mid - 1, best_len, best_pi, best_ti)

        return _binary_search(0, min(m, n), 0, -1, -1)

    def similarity_score(self, pattern, text):
        # Menggunakan versi rekursif untuk pengujian
        L, pi, ti = self.longest_common_substring_recursive(pattern, text)
        if L == 0:
            return 0.0, 0, -1, -1
        return L / len(pattern), L, pi, ti


# ============================================================
# 3. HeapSort (Rekursif)
# ============================================================
class HeapSort:
    @staticmethod
    def higher_priority(a, b):
        if a.length != b.length: return a.length > b.length
        if a.similarity != b.similarity: return a.similarity > b.similarity
        if a.file_name != b.file_name: return a.file_name < b.file_name
        return a.line < b.line

    @classmethod
    def _heapify(cls, arr, n, i):
        largest = i
        l = 2 * i + 1
        r = 2 * i + 2
        if l < n and cls.higher_priority(arr[l], arr[largest]): largest = l
        if r < n and cls.higher_priority(arr[r], arr[largest]): largest = r
        if largest != i:
            arr[i], arr[largest] = arr[largest], arr[i]
            cls._heapify(arr, n, largest) # Rekursif

    @classmethod
    def sort(cls, arr):
        a = list(arr)
        n = len(a)
        for i in range(n // 2 - 1, -1, -1):
            cls._heapify(a, n, i)
        for i in range(n - 1, 0, -1):
            a[0], a[i] = a[i], a[0]
            cls._heapify(a, i, 0)
        return a[::-1]


# ============================================================
# 4. ASTReport & Model
# ============================================================
class ASTReport:
    def __init__(self, pattern, file_name, line, start_index, length, similarity, status):
        self.pattern = pattern
        self.file_name = file_name
        self.line = line
        self.start_index = start_index
        self.length = length
        self.similarity = similarity
        self.status = status

class ASTRecord:
    def __init__(self, file_name, line, ast):
        self.file_name = file_name
        self.line = line
        self.ast = ast

class CorpusLoader:
    @staticmethod
    def load_csv(path):
        records = []
        with open(path, 'r', encoding='utf-8') as f:
            reader = csv.DictReader(f)
            for row in reader:
                records.append(ASTRecord(row['nama_file'], int(row['line']), row['ast'].strip()))
        return records


# ============================================================
# 5. PlagiarismDetector
# ============================================================
class PlagiarismDetector:
    def __init__(self, corpus, patterns):
        self.corpus = corpus
        self.patterns = patterns
        self.rk = RabinKarp()

    def detect(self):
        findings = []
        for pattern in self.patterns:
            found_any = False
            for rec in self.corpus:
                exact_positions = self.rk.exact_search(rec.ast, pattern)
                if exact_positions:
                    for pos in exact_positions:
                        findings.append(ASTReport(pattern, rec.file_name, rec.line, pos, len(pattern), 1.0, "Exact Match"))
                    found_any = True
                else:
                    score, L, pi, ti = self.rk.similarity_score(pattern, rec.ast)
                    if score >= 0.9:
                        findings.append(ASTReport(pattern, rec.file_name, rec.line, ti, L, score, "Partial Match"))
                        found_any = True
            if not found_any:
                findings.append(ASTReport(pattern, "-", -1, -1, 0, 0.0, "Not Found"))
        return findings


# ============================================================
# 6. TestRunner (Simulasi & Pengujian Poin 12, 13)
# ============================================================
def run_simulation():
    print("\n=== SIMULASI SKENARIO PENGUJIAN ===")
    rk = RabinKarp()
    
    # SKENARIO 1: TERBAIK (Exact match di awal, LCS langsung ketemu)
    # Pola dan teks sangat pendek, pencarian langsung berhenti/ketemu
    text_best = "FILCCVFAF"
    pattern_best = "FILCCVFAF"
    rk.comparisons = 0
    start_t = time.perf_counter()
    res_best = rk.exact_search(text_best, pattern_best)
    time_best = time.perf_counter() - start_t
    print(f"1. Skenario Terbaik (Best Case):")
    print(f"   - Teks: {text_best} | Pola: {pattern_best}")
    print(f"   - Hasil: Ditemukan di indeks {res_best}")
    print(f"   - Waktu Eksekusi: {time_best:.6f} detik")
    print(f"   - Total Perbandingan: {rk.comparisons} operasi\n")

    # SKENARIO 2: TERBURUK (Banyak hash collision atau match di akhir)
    # Teks sangat panjang berisi 'V', pola berisi 'V'*m-1 + 'F'
    text_worst = "V" * 500 + "F"
    pattern_worst = "V" * 49 + "F" # Pola panjang 50
    rk.comparisons = 0
    start_t = time.perf_counter()
    res_worst = rk.exact_search(text_worst, pattern_worst)
    time_worst = time.perf_counter() - start_t
    print(f"2. Skenario Terburuk (Worst Case):")
    print(f"   - Teks: 'V' * 500 + 'F' | Pola: 'V' * 49 + 'F'")
    print(f"   - Hasil: Ditemukan di indeks {res_worst}")
    print(f"   - Waktu Eksekusi: {time_worst:.6f} detik")
    print(f"   - Total Perbandingan: {rk.comparisons} operasi\n")

# ============================================================
# Menghitung ukuran memori secara rekursif dalam byte
# ============================================================
import sys

def get_size(obj, seen=None):
    size = sys.getsizeof(obj)
    if seen is None:
        seen = set()
    obj_id = id(obj)
    if obj_id in seen:
        return 0
    seen.add(obj_id)
    if isinstance(obj, dict):
        size += sum([get_size(k, seen) for k in obj.keys()])
        size += sum([get_size(v, seen) for v in obj.values()])
    elif hasattr(obj, '__dict__'):
        size += get_size(obj.__dict__, seen)
    elif hasattr(obj, '__iter__') and not isinstance(obj, (str, bytes, bytearray)):
        size += sum([get_size(i, seen) for i in obj])
    return size

def cetak_ukuran_variabel(corpus, patterns, findings):
    print("\n=== PENGUKURAN UKURAN VARIABEL (BYTES) ===")
    print(f"1. Input 'patterns' (List String)  : {get_size(patterns)} bytes")
    print(f"2. Input 'corpus' (List Objek)     : {get_size(corpus)} bytes")
    print(f"3. Output 'findings' (List Objek)  : {get_size(findings)} bytes")
    
    # Hitung manual (teoretis) untuk perbandingan di video
    panjang_karakter_pattern = sum(len(p) for p in patterns)
    print(f"\n[Fakta Menarik] Panjang karakter asli 'patterns' hanya {panjang_karakter_pattern} karakter.")
    print(f"Namun di Python, ukurannya menjadi {get_size(patterns)} bytes karena ada 'overhead' header objek dan pointer list.")

# ============================================================
# 7. Main
# ============================================================
def main():
    corpus_path = "case4_source_code_ast.csv"
    try:
        corpus = CorpusLoader.load_csv(corpus_path)
    except FileNotFoundError:
        print(f"File {corpus_path} tidak ditemukan. Pastikan file CSV ada di folder yang sama.")
        return

    patterns = ["FILCCVFAF", "RFLCRLROFOCIA", "OOOOOOOOOOOOOOOO"]

    # Mulai pengukuran memori (Poin 12)
    tracemalloc.start()
    start_time = time.perf_counter()

    detector = PlagiarismDetector(corpus, patterns)
    findings = detector.detect()
    sorted_findings = HeapSort.sort(findings)

    end_time = time.perf_counter()
    current_mem, peak_mem = tracemalloc.get_traced_memory()
    tracemalloc.stop()

    print("=== LAPORAN DETEKSI PLAGIARISME TOKENIZED AST (TERURUT PANJANG BLOK) ===")
    print()
    for i, f in enumerate(sorted_findings, 1):
        print(f"{i}. Pola: \"{f.pattern}\"")
        print(f"   File: {f.file_name}")
        print(f"   Baris: {f.line}")
        print(f"   Indeks Awal: {f.start_index}")
        print(f"   Panjang Blok: {f.length}")
        print(f"   Skor Kemiripan: {f.similarity * 100:.1f}%")
        print(f"   Status: {f.status}")
        print()

    print("Metrik Eksekusi:")
    print(f"- Total Operasi Dasar (Perbandingan Karakter): {detector.rk.comparisons} operasi")
    print(f"- Waktu Eksekusi Total: {end_time - start_time:.6f} detik")
    print(f"- Penggunaan Memori Puncak: {peak_mem / 1024:.2f} KB")
    cetak_ukuran_variabel(corpus, patterns, sorted_findings)

    # Jalankan Simulasi
    run_simulation()

if __name__ == "__main__":
    main()