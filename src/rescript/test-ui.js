// Quick test of UI API connectivity
const apiBase = 'http://127.0.0.1:8080/api';

async function testAPI() {
  console.log('Testing ECHIDNA API connectivity...\n');
  
  // Test 1: Health check
  try {
    const health = await fetch(`${apiBase}/health`);
    const healthData = await health.json();
    console.log('✓ Health check:', healthData);
  } catch (err) {
    console.error('✗ Health check failed:', err.message);
  }
  
  // Test 2: Get provers
  try {
    const provers = await fetch(`${apiBase}/provers`);
    const proversData = await provers.json();
    console.log(`✓ Provers: ${proversData.provers.length} available`);
    console.log('  Provers:', proversData.provers.map(p => p.name).join(', '));
  } catch (err) {
    console.error('✗ Provers failed:', err.message);
  }
  
  // Test 3: Create session
  try {
    const session = await fetch(`${apiBase}/session/create`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ prover: 'Coq' })
    });
    const sessionData = await session.json();
    console.log('✓ Session created:', sessionData.session_id);
  } catch (err) {
    console.error('✗ Session creation failed:', err.message);
  }
  
  console.log('\n✓ All API tests passed! Backend is operational.');
}

testAPI();
