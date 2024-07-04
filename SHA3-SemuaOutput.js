class Sha3 {

    // Metode untuk menghasilkan hash SHA-3 256-bit dari pesan
    static hash224(pesan) {
        // Mengatur opsi default untuk padding dan format output
        const opsi = { padding: 'sha-3', msgFormat: 'string', outFormat: 'hex' };
        return Sha3.keccak1600(1152, 448, pesan, opsi);
    }

    static hash256(pesan) {
        // Mengatur opsi default untuk padding dan format output
        const opsi = { padding: 'sha-3', msgFormat: 'string', outFormat: 'hex' };
        return Sha3.keccak1600(1088, 512, pesan, opsi);
    }

    static hash384(pesan) {
        // Mengatur opsi default untuk padding dan format output
        const opsi = { padding: 'sha-3', msgFormat: 'string', outFormat: 'hex' };
        return Sha3.keccak1600(832, 768, pesan, opsi);
    }

    static hash512(pesan) {
        // Mengatur opsi default untuk padding dan format output
        const opsi = { padding: 'sha-3', msgFormat: 'string', outFormat: 'hex' };
        return Sha3.keccak1600(576, 1024, pesan, opsi);
    }

    // Fungsi inti Keccak untuk menghasilkan hash
    static keccak1600(r, c, pesan, opsi) {
        // Opsi default
        const defaults = { padding: 'sha-3', msgFormat: 'string', outFormat: 'hex' };
        const opt = { ...defaults, ...opsi };

        // Menghitung panjang output dalam bit
        const panjangOutputBit = c / 2;

        // Mengonversi pesan ke format UTF-8 jika diperlukan
        let msg = (opt.msgFormat === 'hex-bytes') ? Sha3.hexBytesToString(pesan) : Sha3.utf8Encode(pesan);

        // Menginisialisasi array state Keccak (matriks 5x5 dari BigInt)
        const state = Array.from({ length: 5 }, () => Array(5).fill(0n));

        // Menambahkan padding ke pesan
        const q = (r / 8) - msg.length % (r / 8);
        msg += String.fromCharCode(opt.padding === 'keccak' ? 0x01 : 0x06) + String.fromCharCode(0x00).repeat(q - 2) + String.fromCharCode(0x80);

        // Menyerap pesan ke dalam state
        const ukuranBlok = r / 64 * 8;
        for (let i = 0; i < msg.length; i += ukuranBlok) {
            for (let j = 0; j < r / 64; j++) {
                const x = j % 5;
                const y = Math.floor(j / 5);
                const lane = BigInt.asUintN(64, BigInt(msg.charCodeAt(i + j * 8 + 0)) |
                    BigInt(msg.charCodeAt(i + j * 8 + 1)) << 8n |
                    BigInt(msg.charCodeAt(i + j * 8 + 2)) << 16n |
                    BigInt(msg.charCodeAt(i + j * 8 + 3)) << 24n |
                    BigInt(msg.charCodeAt(i + j * 8 + 4)) << 32n |
                    BigInt(msg.charCodeAt(i + j * 8 + 5)) << 40n |
                    BigInt(msg.charCodeAt(i + j * 8 + 6)) << 48n |
                    BigInt(msg.charCodeAt(i + j * 8 + 7)) << 56n);
                state[x][y] ^= lane;
            }
            Sha3.keccakF1600(state);
        }

        // Mengekstrak hash dari state
        let hash = Sha3.transpose(state)
            .map(plane => plane.map(lane => lane.toString(16).padStart(16, '0').match(/.{2}/g).reverse().join('')).join(''))
            .join('')
            .slice(0, panjangOutputBit / 4);

        // Memformat hash output
        if (opt.outFormat === 'hex-b') hash = hash.match(/.{2}/g).join(' ');
        if (opt.outFormat === 'hex-w') hash = hash.match(/.{8,16}/g).join(' ');

        return hash;
    }

    // Fungsi permutasi Keccak-f[1600]
    static keccakF1600(state) {
        const konstantaPutaran = [
            0x0000000000000001n, 0x0000000000008082n, 0x800000000000808an, 0x8000000080008000n,
            0x000000000000808bn, 0x0000000080000001n, 0x8000000080008081n, 0x8000000000008009n,
            0x000000000000008an, 0x0000000000000088n, 0x0000000080008009n, 0x000000008000000an,
            0x000000008000808bn, 0x800000000000008bn, 0x8000000000008089n, 0x8000000000008003n,
            0x8000000000008002n, 0x8000000000000080n, 0x000000000000800an, 0x800000008000000an,
            0x8000000080008081n, 0x8000000000008080n, 0x0000000080000001n, 0x8000000080008008n,
        ];

        for (let round = 0; round < 24; round++) {
            // Langkah Theta
            const C = Array(5).fill(0n);
            for (let x = 0; x < 5; x++) {
                for (let y = 0; y < 5; y++) C[x] ^= state[x][y];
            }
            const D = Array(5).fill(0n);
            for (let x = 0; x < 5; x++) D[x] = C[(x + 4) % 5] ^ Sha3.rotateLeft(C[(x + 1) % 5], 1);
            for (let x = 0; x < 5; x++) {
                for (let y = 0; y < 5; y++) state[x][y] ^= D[x];
            }

            // Langkah Rho dan Pi
            let [x, y] = [1, 0];
            let current = state[x][y];
            for (let t = 0; t < 24; t++) {
                const [X, Y] = [y, (2 * x + 3 * y) % 5];
                const temp = state[X][Y];
                state[X][Y] = Sha3.rotateLeft(current, ((t + 1) * (t + 2) / 2) % 64);
                current = temp;
                [x, y] = [X, Y];
            }

            // Langkah Chi
            for (let y = 0; y < 5; y++) {
                const C = state.map(row => row[y]);
                for (let x = 0; x < 5; x++) {
                    state[x][y] = C[x] ^ (~C[(x + 1) % 5] & C[(x + 2) % 5]);
                }
            }

            // Langkah Iota
            state[0][0] ^= konstantaPutaran[round];
        }
    }

    // Fungsi untuk menggeser bit ke kiri (rotate left) pada angka 64-bit
    static rotateLeft(value, shift) {
        return BigInt.asUintN(64, (value << BigInt(shift)) | (value >> BigInt(64 - shift)));
    }

    // Fungsi untuk menukar baris dan kolom dalam matriks 2D (transpose)
    static transpose(matrix) {
        return matrix[0].map((_, colIndex) => matrix.map(row => row[colIndex]));
    }

    // Fungsi untuk mengonversi string ke encoding UTF-8
    static utf8Encode(str) {
        return new TextEncoder().encode(str).reduce((prev, curr) => prev + String.fromCharCode(curr), '');
    }

    // Fungsi untuk mengonversi string heksadesimal ke string biasa
    static hexBytesToString(hexStr) {
        return hexStr.match(/.{2}/g).map(byte => String.fromCharCode(parseInt(byte, 16))).join('');
    }
}

module.exports = Sha3;