const express = require('express');
const app = express();
const Sha3 = require('./SHA3-SemuaOutput.js');
const PORT = 3000;

app.use(express.json());

app.get('/', (req, res) => {
    res.send('API is running successfully!');
});

app.post('/hash', (req, res) => {
    const { message, hashType } = req.body;
    let hash;
    switch (hashType) {
        case '224':
            hash = Sha3.hash224(message);
            break;
        case '256':
            hash = Sha3.hash256(message);
            break;
        case '384':
            hash = Sha3.hash384(message);
            break;
        case '512':
            hash = Sha3.hash512(message);
            break;
        default:
            return res.status(400).send('Invalid hash type');
    }
    res.send({ hash });
});

app.listen(PORT, () => {
    console.log(`Server berjalan di http://localhost:${PORT}`);
  });
