import TarGz.Gzip
import TarGz.Tar

/-!
# End-to-end correctness

`create` = tar + gzip (dynamic-Huffman DEFLATE with verified runtime
validation and a verified stored fallback); `extract` = gunzip + untar.
-/

namespace TarGz

def create (es : List TarEntry) : List UInt8 := gzip (tar es)

def extract (bs : List UInt8) : Option (List TarEntry) := (gunzip bs).bind untar

/-- The headline theorem: extracting a created archive yields exactly the
original entries. -/
theorem extract_create (es : List TarEntry) (h : ∀ e ∈ es, ValidEntry e) :
    extract (create es) = some es := by
  unfold extract create
  rw [gunzip_gzip]
  simpa using untar_tar es h

end TarGz
